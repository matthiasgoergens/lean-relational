module

public import Lean
public import Relational.SchemaAudit
public import Relational.SchemaDescription
-- `#describe_schema` builds a `SchemaDescription` while it elaborates
public meta import Relational.SchemaDescription


-- all of it runs while `#describe_schema` elaborates
public meta section

/-! `#describe_schema Snapshot schema` declares `schema.description`, the description of `schema`
(a `SchemaDescription`), which must have passed `#audit_schema`.  It reads the schema at the meta
level, as the audit does, by reducing its values: names, columns and restrictions come from the
tables' own fields, and the columns of a table from the fields of its row structure, with their
Lean types.  Every column name it gives is a top-level field of the row structure, and the names
given to functions are checked against the functions, up to definitional equality, and the build
fails where they differ: a primary or unique key must read the columns its name lists, a foreign
key, a mandatory participation or the owner of a table's rows must read its column and the rows
of the parent table it names, a restriction by values or by a constant relation must read the
columns it names, and an index's and a subtyping's column is the field that its function reads.
The tables' names, and the members and values of the subtypings, are the audit's to check; a
constant relation's name is its own label, given with its rows.  A restriction that is a
predicate is described as an opaque predicate, and so are a participation's scope unless it is
definitionally every parent row and a subtype's family of values.  The description is built when
the module that declares the schema is built, and never committed; `SchemaDescription.write`
writes it as JSON. -/

namespace Relational

open Lean Elab Command Meta Term SchemaMeta

/-- The name of the type `type`, with full names, as the description gives a column's type. -/
private def typeName (type : Expr) : MetaM String := do
  let type ← instantiateMVars type
  withOptions (fun options ↦ pp.fullNames.set options true) do
    return toString (← ppExpr type)

/-- How deeply nested a described value may be: far deeper than any value in a schema. -/
private def valueDepth : Nat := 1000

/-- A value of a discriminating column, as the description gives it: a constructor of an inductive
type that is not a structure by its own short name, followed by its arguments, each given the same
way (a string in quotes, and in parentheses one with arguments of its own), and without its
proofs; a literal as itself; and anything else, such as a structure, as Lean prints it, with full
names.  So `Kind.claim` is `claim` and `Gate.RowOutcome.checked .clash` is `checked clash`. -/
private def valueName (fuel : Nat) (value : Expr) : MetaM String := do
  let fuel' + 1 := fuel | throwError "{value} is nested too deeply to describe"
  let value ← whnf value
  match value with
  | .lit (.natVal number) => return toString number
  | .lit (.strVal text) => return text
  | _ =>
    -- a value of a subtype by its value, the proof that it is one left out
    if value.isAppOfArity ``Subtype.mk 4 then
      if let #[_, _, inner, _] := value.getAppArgs then return ← valueName fuel' inner
    if let .const name _ := value.getAppFn then
      if let .ctorInfo info ← getConstInfo name then
        if value.getAppNumArgs == info.numParams + info.numFields &&
            !isStructure (← getEnv) info.induct then
          let .str _ short := name | throwError "{name} is not a constructor name"
          let mut words := #[short]
          for field in value.getAppArgs[info.numParams:] do
            if ← Meta.isProof field then continue
            let field ← whnf field
            let word ← match field with
              | .lit (.strVal text) => pure text.quote
              | _ => valueName fuel' field
            words := words.push (if word.contains ' ' && !word.startsWith "\"" then s!"({word})"
              else word)
          return " ".intercalate words.toList
    withOptions (fun options ↦ pp.fullNames.set options true) do
      return toString (← ppExpr value)

/-- The two components of the pair that `pair` reduces to, if it is one. -/
private def pairParts (pair : Expr) : MetaM (Option (Expr × Expr)) := do
  let pair ← whnf pair
  if pair.isAppOfArity ``Prod.mk 4 then
    if let #[_, _, first, second] := pair.getAppArgs then return some (first, second)
  return none

/-- The arguments of the constructor application that `term` reduces to, by the names of the
constructor's parameters and fields. -/
private def constructorArguments (term : Expr) : MetaM (Name × Array (Name × Expr)) := do
  let term ← whnf term
  let some name := term.getAppFn.constName? | throwError "{term} is not a constructor application"
  let .ctorInfo info ← getConstInfo name | throwError "{term} is not a constructor application"
  let names ← forallTelescopeReducing info.type fun binders _ ↦
    binders.mapM fun binder ↦ return (← getFVarLocalDecl binder).userName
  unless names.size == term.getAppNumArgs do
    throwError "{term} is not a full application of {name}"
  return (name, names.zip term.getAppArgs)

/-- The argument named `name` of a constructor application. -/
private def argument (arguments : Array (Name × Expr)) (name : Name) : MetaM Expr := do
  let some (_, value) := arguments.find? (·.1 == name) | throwError "no argument {name}"
  return value

/-- Fails unless `function` reads the column `column` of rows of type `row`. -/
private def checkColumn (function row : Expr) (column : String) (what : MessageData) :
    MetaM Unit := do
  checkTopLevel row column what
  unless ← isDefEq function (← columnFunction row column.toName) do
    throwError "{what} does not read the column {column}"

/-- Fails unless `function` reads the columns `columns` of rows of type `row`, separated by commas:
one column, or several read as a tuple, for a foreign key or a mandatory participation into a table
whose primary key has several. -/
private def checkColumns (function row : Expr) (columns : String) (what : MessageData) :
    MetaM Unit := do
  for column in columns.splitOn ", " do checkTopLevel row column what
  unless ← isDefEq function (← keyFunction row columns what) do
    throwError "{what} does not read the columns {columns}"

/-- Fails unless `parents`, a function of a snapshot of type `snapshot`, reads the rows of the
table named `parent` among `tables`, as a relation. -/
private def checkParent (parents snapshot : Expr) (tables : Array (String × Expr)) (parent : String)
    (what : MessageData) : MetaM Unit := do
  let some (_, entry) := tables.find? (·.1 == parent)
    | throwError "{what} refers to {parent}, which is not a table of the schema"
  let read ← mkAppM ``Table.rows #[← mkAppM ``AnyTable.table #[entry]]
  let expected ← withLocalDeclD `rows snapshot fun rows ↦ do
    mkLambdaFVars #[rows] (← mkAppM ``Rows.toRelation #[mkApp read rows])
  unless ← isDefEq parents expected do throwError "{what} does not read the rows of {parent}"

/-- The constant relation of allowed parents `relation`. -/
private def describeAllowance (relation : Expr) : MetaM AllowanceDescription := do
  let name ← stringOf (← mkAppM ``Allowance.name #[relation])
  let type ← whnf (← inferType relation)
  let #[child, endpoint, parent] := type.getAppArgs
    | throwError "{relation} is not an Allowance but of type {type}"
  let rows ← (← elementsOf (← mkAppM ``Allowance.rows #[relation])).mapM fun row ↦ do
    let some (child, rest) ← pairParts row
      | throwError "a row of {name} does not reduce to a triple: {row}"
    let some (endpoint, parent) ← pairParts rest
      | throwError "a row of {name} does not reduce to a triple: {row}"
    return { child := ← valueName valueDepth child, endpoint := ← valueName valueDepth endpoint
             parent := ← valueName valueDepth parent }
  return { name, childType := ← typeName child, endpointType := ← typeName endpoint
           parentType := ← typeName parent, rows := rows.toList }

/-- The restriction `restriction` of the foreign key `what` from rows of type `row` to rows of
type `parent`, and the constant relation it uses, if any. -/
private def describeRestriction (restriction row parent : Expr) (what : MessageData) :
    MetaM (RestrictionDescription × Option AllowanceDescription) := do
  let (constructor, arguments) ← constructorArguments restriction
  match constructor with
  | ``Restriction.any => return (.any, none)
  | ``Restriction.facts =>
    let column ← stringOf (← argument arguments `column)
    checkColumn (← argument arguments `fact) parent column m!"the restriction of {what}"
    let values ← (← elementsOf (← argument arguments `values)).mapM (valueName valueDepth)
    return (.facts column values.toList, none)
  | ``Restriction.allowance =>
    let childColumn ← stringOf (← argument arguments `childColumn)
    checkColumn (← argument arguments `child) row childColumn m!"the restriction of {what}"
    let parentColumn ← stringOf (← argument arguments `parentColumn)
    checkColumn (← argument arguments `fact) parent parentColumn m!"the restriction of {what}"
    let allowance ← describeAllowance (← argument arguments `relation)
    let endpoint ← valueName valueDepth (← argument arguments `endpoint)
    return (.allowance childColumn allowance.name endpoint parentColumn, some allowance)
  | ``Restriction.predicate => return (.predicate, none)
  | _ => throwError "the restriction of {what} is not a Restriction but {restriction}"

/-- The table of the entry `entry` of the schema's tables `tables`, of a snapshot of type
`snapshot`, and the constant relations its foreign keys use. -/
private def describeTable (snapshot : Expr) (tables : Array (String × Expr)) (entry : Expr) :
    MetaM (TableDescription × Array AllowanceDescription) := do
  let table ← mkAppM ``AnyTable.table #[entry]
  let name ← stringOf (← mkAppM ``Table.name #[table])
  let row ← whnf (← mkAppM ``AnyTable.Row #[entry])
  let (_, fields) ← fieldsOf row
  let columns ← fields.mapM fun field ↦ do
    let type ← withLocalDeclD `row row fun value ↦ do inferType (← mkProjection value field)
    return ({ name := field.toString, type := ← typeName type } : ColumnDescription)
  let primaryName ← stringOf (← mkAppM ``Table.primaryName #[table])
  let primary ← keyFunction row primaryName m!"the primary key of {name}"
  unless ← isDefEq (← mkAppM ``AnyTable.key #[entry]) primary do
    throwError "the primary key of {name} is not ({primaryName})"
  let uniqueKeys ← (← elementsOf (← mkAppM ``Table.uniqueKeys #[table])).mapM fun unique ↦ do
    let key ← stringOf (← mkAppM ``UniqueKey.name #[unique])
    let read ← keyFunction row key m!"the unique key ({key}) of {name}"
    unless ← isDefEq (← mkAppM ``UniqueKey.key #[unique]) read do
      throwError "the unique key ({key}) of {name} is not those columns"
    return keyColumns key fields
  let mut foreignKeys := #[]
  let mut allowances := #[]
  for foreign in ← elementsOf (← mkAppM ``Table.foreignKeys #[table]) do
    let column ← stringOf (← mkAppM ``ForeignKey.column #[foreign])
    let what := m!"the foreign key {column} of {name}"
    checkColumns (← mkAppM ``ForeignKey.reference #[foreign]) row column what
    let parent ← stringOf (← mkAppM ``ForeignKey.parentName #[foreign])
    checkParent (← mkAppM ``ForeignKey.parents #[foreign]) snapshot tables parent what
    let parentRow ← whnf (← mkAppM ``ForeignKey.Parent #[foreign])
    let (restriction, allowance) ←
      describeRestriction (← mkAppM ``ForeignKey.restriction #[foreign]) row parentRow what
    foreignKeys := foreignKeys.push ({ column, parent, restriction } : ForeignKeyDescription)
    allowances := allowances ++ allowance.toArray
  let participations ← elementsOf (← mkAppM ``Table.participations #[table])
  let mandatory ← participations.mapM fun participation ↦ do
    let column ← stringOf (← mkAppM ``Participation.column #[participation])
    let what := m!"the mandatory participation {column} of {name}"
    checkColumns (← mkAppM ``Participation.reference #[participation]) row column what
    let parent ← stringOf (← mkAppM ``Participation.parentName #[participation])
    checkParent (← mkAppM ``Participation.parents #[participation]) snapshot tables parent what
    let parentRow ← whnf (← mkAppM ``Participation.Parent #[participation])
    let everyRow ← withLocalDeclD `parent parentRow fun value ↦
      mkLambdaFVars #[value] (Lean.mkConst ``Bool.true)
    let scope : ScopeDescription :=
      if ← isDefEq (← mkAppM ``Participation.scope #[participation]) everyRow then .all
      else .predicate
    return ({ column, parent, scope } : ParticipationDescription)
  let indexes ← (← elementsOf (← mkAppM ``Table.indexes #[table])).mapM fun index ↦ do
    let indexName ← stringOf (← mkAppM ``TableIndex.name #[index])
    let some column ← columnOf? row (← mkAppM ``TableIndex.column #[index])
      | throwError "the index {indexName} of {name} is not by a column of its rows"
    return ({ name := indexName, column := column.toString } : IndexDescription)
  let ownership ← whnf (← mkAppM ``Table.ownership #[table])
  let owner ← match ownership.getAppFn.constName? with
    | some ``Ownership.root => pure .root
    | some ``Ownership.loaded => pure .loaded
    | some ``Ownership.owned =>
      let .app _ found := ownership | throwError "{ownership} is not an application"
      let column ← stringOf (← mkAppM ``Owner.column #[found])
      let what := m!"the owner of the rows of {name}"
      checkColumn (← mkAppM ``Owner.reference #[found]) row column what
      let parent ← stringOf (← mkAppM ``Owner.ownerName #[found])
      checkParent (← mkAppM ``Owner.parents #[found]) snapshot tables parent what
      pure (.owned column parent)
    | _ => throwError "{name} declares no owner of its rows"
  return ({ name, columns := columns.toList, primaryKey := keyColumns primaryName fields
            uniqueKeys := uniqueKeys.toList, foreignKeys := foreignKeys.toList
            mandatory := mandatory.toList, indexes := indexes.toList, owner }, allowances)

/-- The subtyping `subtyping`. -/
private def describeSubtyping (subtyping : Expr) : MetaM SubtypingDescription := do
  let supertype ← stringOf (← mkAppM ``Subtyping.name #[subtyping])
  let row ← whnf (← mkAppM ``AnyTable.Row #[← mkAppM ``Subtyping.supertype #[subtyping]])
  let some discriminator ← columnOf? row (← mkAppM ``Subtyping.fact #[subtyping])
    | throwError "a subtyping of {supertype} does not discriminate by a column of its rows"
  let members ← (← elementsOf (← mkAppM ``Subtyping.members #[subtyping])).mapM fun member ↦ do
    let table ← stringOf (← mkAppM ``SubtypeMember.name #[member])
    let (constructor, arguments) ← constructorArguments (← mkAppM ``SubtypeMember.facts #[member])
    let facts ← match constructor with
      | ``FactSet.values =>
        pure (.values (← (← elementsOf (← argument arguments `values)).mapM (valueName valueDepth)).toList)
      | ``FactSet.family => pure .predicate
      | _ => throwError "the values of the subtype {table} of {supertype} are not a FactSet"
    return ({ table, facts } : SubtypeDescription)
  let coverage ← match (← whnf (← mkAppM ``Subtyping.coverage #[subtyping])).constName? with
    | some ``Coverage.none => pure .none
    | some ``Coverage.covering => pure .covering
    | some ``Coverage.exhaustive => pure .exhaustive
    | _ => throwError "the coverage of a subtyping of {supertype} does not reduce to a constructor"
  return { supertype, discriminator := discriminator.toString, members := members.toList, coverage }

/-- The description of the schema `schema` of the snapshot structure `snapshot`. -/
def describeSchema (snapshot schema : Name) : MetaM SchemaDescription := do
  let snapshotType := Lean.mkConst snapshot
  let schemaValue := Lean.mkConst schema
  unless ← isDefEq (← inferType schemaValue) (mkApp (Lean.mkConst ``Schema) snapshotType) do
    throwError "{schema} is not a schema of {snapshot}"
  if (← synthInstance? (← mkAppM ``Audited #[schemaValue])).isNone then
    throwError "{schema} has not passed #audit_schema"
  let entries ← elementsOf (← mkAppM ``Schema.tables #[schemaValue])
  let tables ← entries.mapM fun entry ↦ do
    return (← stringOf (← mkAppM ``Table.name #[← mkAppM ``AnyTable.table #[entry]]), entry)
  let mut described := #[]
  let mut allowances : Array AllowanceDescription := #[]
  for entry in entries do
    let (table, used) ← describeTable snapshotType tables entry
    described := described.push table
    for allowance in used do
      match allowances.find? (·.name == allowance.name) with
      | some known =>
        unless known == allowance do
          throwError "two different constant relations are named {allowance.name}"
      | none => allowances := allowances.push allowance
  let subtypings ← (← elementsOf (← mkAppM ``Schema.subtypings #[schemaValue])).mapM
    describeSubtyping
  return { snapshot := snapshot.toString, tables := described.toList
           subtypings := subtypings.toList, allowances := allowances.toList }

elab "#describe_schema " snapshot:ident schema:ident : command => do
  let (schemaName, description) ← liftTermElabM do
    let snapshotName ← realizeGlobalConstNoOverloadWithInfo snapshot
    let schemaName ← realizeGlobalConstNoOverloadWithInfo schema
    return (schemaName, ← describeSchema snapshotName schemaName)
  liftTermElabM do
    let name := schemaName ++ `description
    addAndCompile <| .defnDecl {
      name, levelParams := [], type := Lean.mkConst ``SchemaDescription
      value := toExpr description, hints := .opaque, safety := .safe }

end Relational
