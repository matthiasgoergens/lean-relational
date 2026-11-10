module

public import Lean
public import Relational.Database
-- `#audit_schema` builds the schema's `Audited` instance with `auditedConstructor`
public meta import Relational.Database


-- all of it runs while `#audit_schema` and `#describe_schema` elaborate
public meta section

/-! `#audit_schema Snapshot schema` fails the build unless `schema` covers the structure
`Snapshot`, and then declares that it passed (`Audited schema`, which `Db.load` and `Db.append`
require) and where each table sits in the schema, so that inserts can name it.  Every field `f`
of `Snapshot`, its own and those it inherits, holds `Rows` or an `Index`.  For a field holding
`Rows`, the constant `f` in the namespace of `schema` is a table that reads the field, is named
`"f"` and replaces that field, its primary key reads the columns that its name lists, and
`schema.tables` lists these tables in field order.  A field holding an `Index` is maintained by
exactly one of these tables, and every index that a table maintains reads and replaces a field
holding an `Index`, of the index's name.  Every subtyping's supertype and members are tables of
the schema, no member is listed twice, for an empty list of values or for a list with a value
twice, an exhaustive subtyping has a member, and the subtyping discriminates by a column of the
supertype's rows, so that what it checks of a member's rows (`Subtyping.Typed`) is the value of
that column, not a predicate of the whole row that may accept anything; a member for a family of
values is a predicate of that value only.
Every table declares who owns its rows (`root%`, `owner%` or `loaded%`): an owner is a table of
the schema, a root or itself owned, that the owned rows refer to through a column, by a foreign
key or as a subtype of it, the owners form no cycle, and a root table is neither a subtype nor
refers to a table that owns rows through a column of its primary key, so that `Schema.Frozen`
rests on declared, checked owners.  A table whose primary key is its own is trusted to be a root
when it says so (`auditRoot`).  The checks compare the
values of the schema and the tables up to definitional equality, so how a table is written does
not matter.  The audit declares the instance `schema.instAudited`, and for every
table `f` the instance `schema.f : InSchema schema f`, proved from the declarations in
`schema.positions`: the tables from each position on (`from<k>`, which nothing runs), the
schema's tables as those from the first (`tables_eq`), their number (`length`), and what dropping
the first `k` leaves (`drop<k>`). -/

namespace Relational

open Lean Elab Command Meta Term

namespace SchemaMeta

/-! What the schema audit and the schema description share: reading a schema's values at the meta
level, by reducing them.  This code runs while `#audit_schema` and `#describe_schema` elaborate,
so each error it throws fails the build at that command; none of it runs in a compiled program. -/

/-- The term written as `syntax_`, elaborated. -/
def elaborated (syntax_ : Term) : TermElabM Expr := do
  let value ← elabTerm syntax_ none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

/-- The function that reads the field `field` of a `snapshot`, own or inherited. -/
def projectionOf (snapshot field : Name) : TermElabM Expr := do
  elaborated (← `(fun ($(mkIdent `snapshot) : $(mkIdent snapshot)) ↦ $(mkIdent (`snapshot ++ field))))

/-- The function that replaces the field `field` of a `snapshot`, as `table%` writes it. -/
def setterOf (snapshot field : Name) : TermElabM Expr := do
  elaborated (← `(fun (snapshot : $(mkIdent snapshot)) value ↦
    { snapshot with $(mkIdent field):ident := value }))

/-- The function that reads the table `table` of a `snapshot` from the group field `group` that
holds it (`table_rows%`), written out here rather than taken from the reader it declares. -/
def groupProjectionOf (snapshot group table : Name) : TermElabM Expr := do
  elaborated (← `(fun ($(mkIdent `snapshot) : $(mkIdent snapshot)) ↦
    $(mkIdent (`snapshot ++ group)).$(mkIdent table):ident))

/-- The function that replaces the table `table` in its group field `group` of a `snapshot`,
written out here rather than taken from the setter `table_rows%` declares. -/
def groupSetterOf (snapshot group table : Name) : TermElabM Expr := do
  let snapshotVar := mkIdent `snapshot
  elaborated (← `(fun ($snapshotVar : $(mkIdent snapshot)) value ↦
    { $snapshotVar with $(mkIdent group):ident :=
      { $(mkIdent (`snapshot ++ group)) with $(mkIdent table):ident := value } }))

/-- The elements of the list `list`, which must reduce to a list literal. -/
partial def elementsOf  -- principles: ignore[lean:partial-def] runs at elaboration; whnf may grow the term
    (list : Expr) : MetaM (Array Expr) := do
  let list ← whnf list
  if list.isAppOfArity ``List.cons 3 then
    let #[_, head, tail] := list.getAppArgs | throwError "{list} is not a full list cons"
    return #[head] ++ (← elementsOf tail)
  else if list.isAppOfArity ``List.nil 1 then
    return #[]
  else throwError "{list} does not reduce to a list"

/-- The string literal that `term` reduces to. -/
def stringOf (term : Expr) : MetaM String := do
  match ← whnf term with
  | .lit (.strVal value) => return value
  | reduced => throwError "{term} does not reduce to a string literal but to {reduced}"

/-- The structure that the row type `row` reduces to, and its fields, own and inherited. -/
def fieldsOf (row : Expr) : MetaM (Name × Array Name) := do
  let row ← whnf row
  let some structure_ := row.getAppFn.constName?
    | throwError "{row} is not a structure type"
  unless isStructure (← getEnv) structure_ do throwError "{row} is not a structure type"
  let fields := getStructureFieldsFlattened (← getEnv) structure_ (includeSubobjectFields := false)
  return (structure_, fields)

/-- The function that reads the column `column` of a row of type `row`: a field, own or inherited,
or a path of fields separated by dots. -/
def columnFunction (row : Expr) (column : Name) : MetaM Expr :=
  withLocalDeclD `row row fun value ↦ do
    mkLambdaFVars #[value] (← column.components.foldlM mkProjection value)

/-- The field of the row type `row`, own or inherited, that `function` reads, if any. -/
def columnOf? (row function : Expr) : MetaM (Option Name) := do
  let (_, fields) ← fieldsOf row
  fields.findM? fun field ↦ do isDefEq function (← columnFunction row field)

/-- The columns of a key named `name`, as `table%` names it: columns separated by commas, or `*`
for the whole row, of the fields `fields`. -/
def keyColumns (name : String) (fields : Array Name) : List String :=
  if name == "*" then -- principles: ignore[lean:string-compare] `*` is the whole-row key's syntax, no vocabulary
    fields.toList.map (·.toString) else name.splitOn ", "

/-- Fails unless `column` is a top-level field of rows of type `row`, as the description lists the
columns: not a path through a nested field. -/
def checkTopLevel (row : Expr) (column : String) (what : MessageData) : MetaM Unit := do
  let (_, fields) ← fieldsOf row
  unless fields.any (·.toString == column) do

    throwError "{what} names {column}, which is not a column of its rows"

/-- The function that reads the key named `name` of a row of type `row`, as `table%` writes it. -/
def keyFunction (row : Expr) (name : String) (what : MessageData) : MetaM Expr :=
  withLocalDeclD `row row fun value ↦ do
    if name == "*" then -- principles: ignore[lean:string-compare] `*` is the whole-row key's syntax, no vocabulary
      return ← mkLambdaFVars #[value] value
    let columns ← (name.splitOn ", ").mapM fun column ↦ do
      checkTopLevel row column what
      column.toName.components.foldlM mkProjection value
    let some last := columns.getLast? | throwError "a key without columns"
    let tuple ← columns.dropLast.foldrM (fun column rest ↦ mkAppM ``Prod.mk #[column, rest]) last
    mkLambdaFVars #[value] tuple

/-- The structure of the group field `field` of `snapshot`, if it is one that `table_rows%` declares
(`<Holder>Group<k>`, of the structure `<Holder>.Group<k>`), which stands for the tables in it. -/
def groupOf? (snapshot field : Name) : TermElabM (Option Name) := do
  let type ← inferType (← projectionOf snapshot field)
  let held ← forallTelescope type fun _ body ↦ instantiateMVars body
  return match (← whnf held).getAppFn.constName? with
    | some (.str holder@(.str _ holderLast) last) =>
      if last.startsWith "Group" && field == Name.mkSimple (holderLast ++ last) then
        some (.str holder last)
      else none
    | _ => none

end SchemaMeta

open SchemaMeta

/-- Fails unless the table `table` reads, names and replaces the field `field` of `snapshot`, or,
where `group?` names the group field that holds it (`table_rows%`), that field's field `field`. -/
private def auditTable (snapshot field table : Name) (group? : Option Name := none) :
    TermElabM Unit := do
  let rows ← mkAppM ``Table.rows #[Lean.mkConst table]
  let reads ← match group? with
    | some group => groupProjectionOf snapshot group field
    | none => projectionOf snapshot field
  unless ← isDefEq rows reads do
    throwError "{table} does not read the field {field} of {snapshot}"
  let name ← mkAppM ``Table.name #[Lean.mkConst table]
  unless ← isDefEq name (toExpr field.toString) do
    throwError "{table} is not named {field}"
  let set ← mkAppM ``Table.set #[Lean.mkConst table]
  let replaces ← match group? with
    | some group => groupSetterOf snapshot group field
    | none => setterOf snapshot field
  unless ← isDefEq set replaces do
    throwError "{table} does not replace the field {field}"

/-- Fails unless every index of `table` reads and replaces a field of `snapshot` among `indexes`,
of the index's name; returns those fields. -/
private def auditIndexes (snapshot table : Name) (indexes : Array Name) : TermElabM (Array Name) := do
  let mut maintained := #[]
  for index in ← elementsOf (← mkAppM ``Table.indexes #[Lean.mkConst table]) do
    let name ← stringOf (← mkAppM ``TableIndex.name #[index])
    let field := Name.mkSimple name
    unless indexes.contains field do
      throwError "{table} maintains an index {name}, which is not a field of {snapshot} holding \
        an Index"
    unless ← isDefEq (← mkAppM ``TableIndex.get #[index]) (← projectionOf snapshot field) do
      throwError "the index {name} of {table} does not read the field {field}"
    unless ← isDefEq (← mkAppM ``TableIndex.set #[index]) (← setterOf snapshot field) do
      throwError "the index {name} of {table} does not replace the field {field}"
    maintained := maintained.push field
  return maintained

/-- Fails unless the subtyping `subtyping` of the table `supertype` discriminates by a column of
the supertype's rows, own or inherited. -/
private def auditDiscriminator (subtyping : Expr) (supertype : Name) : TermElabM Unit := do
  let row ← whnf (← mkAppM ``AnyTable.Row #[← mkAppM ``Subtyping.supertype #[subtyping]])
  let some structure_ := row.getAppFn.constName?
    | throwError "the rows of {supertype} are not of a structure type but {row}"
  unless isStructure (← getEnv) structure_ do
    throwError "the rows of {supertype} are not of a structure type but {row}"
  if (← columnOf? row (← mkAppM ``Subtyping.fact #[subtyping])).isNone then
    throwError "a subtyping of {supertype} does not discriminate by a column of its rows"

/-- Fails unless the supertype and the members of every subtyping of `schema` are tables of it
(in `space`, among `tables`), no member is listed twice, for an empty list of values or for a list
with a value twice (equal up to definitional equality), an exhaustive subtyping has a member, which
would otherwise refuse every supertype row, and the subtyping discriminates by a column of the
supertype's rows. -/
private def auditSubtypings (schema space : Name) (tables : Array Name) :
    TermElabM Unit := do
  for subtyping in ← elementsOf (← mkAppM ``Schema.subtypings #[Lean.mkConst schema]) do
    let supertypeName ← stringOf (← mkAppM ``Subtyping.name #[subtyping])
    let supertype := space ++ Name.mkSimple supertypeName
    unless tables.contains supertype do
      throwError "the supertype {supertypeName} of a subtyping is not a table of {schema}"
    unless ← isDefEq (← mkAppM ``Subtyping.supertype #[subtyping])
        (← mkAppM ``AnyTable.mk #[Lean.mkConst supertype]) do
      throwError "the supertype of a subtyping named {supertypeName} is not the table {supertype}"
    auditDiscriminator subtyping supertype
    let mut seen : Array Name := #[]
    for member in ← elementsOf (← mkAppM ``Subtyping.members #[subtyping]) do
      let memberName ← stringOf (← mkAppM ``SubtypeMember.name #[member])
      let table := space ++ Name.mkSimple memberName
      unless tables.contains table do
        throwError "the subtype {memberName} of {supertypeName} is not a table of {schema}"
      if seen.contains table then
        throwError "the subtype {memberName} is listed twice for {supertypeName}"
      seen := seen.push table
      let facts ← mkAppM ``SubtypeMember.facts #[member]
      unless ← isDefEq member (← mkAppM ``SubtypeMember.of #[Lean.mkConst table, facts]) do
        throwError "the subtype named {memberName} of {supertypeName} is not the table {table}"
      let facts ← whnf facts
      if facts.isAppOfArity ``FactSet.values 2 then
        let some valuesList := facts.getAppArgs.back?
          | throwError "{facts} has no values"
        let values ← elementsOf valuesList
        if values.isEmpty then
          throwError "the subtype {memberName} of {supertypeName} is for no value"
        for h : i in [0:values.size] do
          for earlier in values[0:i] do
            if ← isDefEq earlier values[i] then
              throwError "the subtype {memberName} of {supertypeName} lists the value \
                {values[i]} twice"
    if seen.isEmpty &&
        (← whnf (← mkAppM ``Subtyping.coverage #[subtyping])).isAppOf ``Coverage.exhaustive then
      throwError "an exhaustive subtyping of {supertypeName} has no member, so it refuses every row"

/-- The rows of the table `table` as a relation, as a function of a snapshot of the type that
`parents`, a function of a snapshot, takes. -/
private def rowsOfTable (table : Name) (parents : Expr) : MetaM Expr := do
  let .forallE _ snapshot _ _ ← whnf (← inferType parents)
    | throwError "{parents} is not a function of a snapshot"
  withLocalDeclD `rows snapshot fun rows ↦ do
    mkLambdaFVars #[rows] (← mkAppM ``Rows.toRelation
      #[mkApp (← mkAppM ``Table.rows #[Lean.mkConst table]) rows])

/-- Fails unless the root table `table`, with rows of type `row`, owns its rows: it is no subtype
(a member of a subtyping in `subtypes`, by member and supertype), and no column of its primary key
is a foreign key into a table among `owners`, the tables that declare `root%` or `owner%`.  The
rows of either belong to another table's rows, and declared `root%` they would escape
`Table.Frozen`: a new row for an old owner would be a new root.  The rest is trusted: a table
whose primary key is its own, with the reference to its owner outside it, may be a relation whose
rows are their own owners, as an edge is, or an attribute with a surrogate key, which the audit
cannot tell apart; and a table that refers to another without a declared foreign key shows the
audit no reference at all. -/
private def auditRoot (table : Name) (row : Expr) (subtypes : Array (Name × Name))
    (owners : Array Name) : TermElabM Unit := do
  if let some (_, supertype) := subtypes.find? (·.1 == table) then
    throwError "{table} declares root%, but it is a subtype of {supertype}, whose rows its rows \
      belong to: owner%"
  let (_, fields) ← fieldsOf row
  let primaryColumns := keyColumns (← stringOf (← mkAppM ``Table.primaryName #[Lean.mkConst table]))
    fields
  for foreign in ← elementsOf (← mkAppM ``Table.foreignKeys #[Lean.mkConst table]) do
    let some column ← columnOf? row (← mkAppM ``ForeignKey.reference #[foreign]) | continue
    unless primaryColumns.contains column.toString do continue
    let parents ← mkAppM ``ForeignKey.parents #[foreign]
    for owner in owners do
      if ← isDefEq parents (← rowsOfTable owner parents) then
        throwError "{table} declares root%, but the column {column} of its primary key is a \
          foreign key into {owner}, which owns rows (root% or owner%), whose rows its rows \
          belong to: owner%"

/-- Fails unless every table of `schema` (in `space`, among `tables`) declares who owns its rows:
a root table (`root%`) that is no subtype and has no column of its primary key referring to a
table that owns rows (`auditRoot`), a table only the loader writes (`loaded%`), or a table each of
whose rows belongs to a row of an owner table of the schema (`owner%`), itself a root or owned,
through a column that the owner function reads and that is either a foreign key into the owner
table or, for a subtype of the owner table, its whole primary key; and the owners form no cycle,
so that following them from any owned table ends at a root table.  So a row's owner is a row of
the owner table whenever the snapshot is valid, and `Table.Frozen` holds by induction along the
owners: a new row's owner is new, since the owner table refuses a new row of an old owner in its
turn, and so on up to a new root row.  The owner column need not be part of the primary key: `Table.Frozen` refuses a
new row of an old owner whatever its key, and with `Schema.Extends` a row that exists stays, so that no
other row can take its key; the rows of an old owner then neither change nor grow in number. -/
private def auditOwners (schema space : Name) (tables : Array Name) : TermElabM Unit := do
  let mut subtypes : Array (Name × Name) := #[]
  for subtyping in ← elementsOf (← mkAppM ``Schema.subtypings #[Lean.mkConst schema]) do
    let supertype := space ++ Name.mkSimple (← stringOf (← mkAppM ``Subtyping.name #[subtyping]))
    for member in ← elementsOf (← mkAppM ``Subtyping.members #[subtyping]) do
      let name ← stringOf (← mkAppM ``SubtypeMember.name #[member])
      subtypes := subtypes.push (space ++ Name.mkSimple name, supertype)
  let owners ← tables.filterM fun table ↦ do
    let ownership ← whnf (← mkAppM ``Table.ownership #[Lean.mkConst table])
    return ownership.isAppOf ``Ownership.root || ownership.isAppOf ``Ownership.owned
  let mut ownerOf : Array (Name × Name) := #[]
  for table in tables do
    let entry ← mkAppM ``AnyTable.mk #[Lean.mkConst table]
    let row ← whnf (← mkAppM ``AnyTable.Row #[entry])
    let ownership ← whnf (← mkAppM ``Table.ownership #[Lean.mkConst table])
    if ownership.isAppOf ``Ownership.loaded then continue
    if ownership.isAppOf ``Ownership.root then
      auditRoot table row subtypes owners
      continue
    unless ownership.isAppOf ``Ownership.owned do
      throwError "{table} declares no owner of its rows: root%, owner% or loaded%"
    let some owner := ownership.getAppArgs.back?
      | throwError "the ownership of {table} has no owner"
    let column ← stringOf (← mkAppM ``Owner.column #[owner])
    let ownerName ← stringOf (← mkAppM ``Owner.ownerName #[owner])
    let ownerTable := space ++ Name.mkSimple ownerName
    unless tables.contains ownerTable do
      throwError "the owner {ownerName} of the rows of {table} is not a table of {schema}"
    unless owners.contains ownerTable do
      throwError "the owner {ownerName} of the rows of {table} owns no rows (root% or owner%)"
    let parents ← mkAppM ``Owner.parents #[owner]
    unless ← isDefEq parents (← rowsOfTable ownerTable parents) do
      throwError "the owner of the rows of {table} does not read the rows of {ownerTable}"
    let reference ← mkAppM ``Owner.reference #[owner]
    unless (← columnOf? row reference) == some column.toName do
      throwError "the owner of the rows of {table} does not read the column {column}"
    let foreignKeys ← elementsOf (← mkAppM ``Table.foreignKeys #[Lean.mkConst table])
    let byForeignKey ← foreignKeys.anyM fun foreign ↦ do
      return (← stringOf (← mkAppM ``ForeignKey.parentName #[foreign])) == ownerName &&
        (← isDefEq (← mkAppM ``ForeignKey.reference #[foreign]) reference) &&
        (← isDefEq (← mkAppM ``ForeignKey.parents #[foreign]) parents)
    let bySubtyping := subtypes.contains (table, ownerTable) &&
      (← isDefEq (← mkAppM ``AnyTable.key #[entry]) reference)
    unless byForeignKey || bySubtyping do
      throwError "the owner column {column} of {table} is neither a foreign key into {ownerName} \
        nor the primary key of a subtype of it"
    ownerOf := ownerOf.push (table, ownerTable)
  for (table, _) in ownerOf do
    let mut path := #[table]
    let mut current := table
    while  -- principles: ignore[lean:while-loop] runs at elaboration, stops on its cycle check; rewrite queued
        true do
      let some (_, next) := ownerOf.find? (·.1 == current) | break
      if path.contains next then
        throwError "following the owners from {table} runs in a cycle: \
          {" → ".intercalate ((path.push next).toList.map toString)}"
      path := path.push next
      current := next

/-- Fails unless the primary key of the table `table` reads the columns that its name lists, so
that the name, which diagnostics and the description give and `auditRoot` reads, is the key's. -/
private def auditPrimaryKey (table : Name) : TermElabM Unit := do
  let entry ← mkAppM ``AnyTable.mk #[Lean.mkConst table]
  let row ← whnf (← mkAppM ``AnyTable.Row #[entry])
  let primaryName ← stringOf (← mkAppM ``Table.primaryName #[Lean.mkConst table])
  let primary ← keyFunction row primaryName m!"the primary key of {table}"
  unless ← isDefEq (← mkAppM ``AnyTable.key #[entry]) primary do
    throwError "the primary key of {table} is not ({primaryName})"

elab "#audit_schema " snapshot:ident schema:ident : command => do
  let (schemaName, snapshotName, tables) ← liftTermElabM do
    let snapshotName ← realizeGlobalConstNoOverloadWithInfo snapshot
    let schemaName ← realizeGlobalConstNoOverloadWithInfo schema
    let space := schemaName.getPrefix
    let env ← getEnv
    unless isStructure env snapshotName do throwError "{snapshotName} is not a structure"
    let mut tables : Array Name := #[]
    let mut indexes : Array Name := #[]
    -- a group field `table_rows%` declares (`<Holder>Group<k>`, of the structure `<Holder>.Group<k>`)
    -- stands for the tables in it; any other field holds Rows or an Index, as below
    let mut leaves : Array (Name × Option Name) := #[]
    for field in getStructureFieldsFlattened env snapshotName (includeSubobjectFields := false) do
      match ← groupOf? snapshotName field with
      | some group =>
        unless isStructure env group do throwError "the group field {field} holds no structure"
        let inner := getStructureFieldsFlattened env group (includeSubobjectFields := false)
        if inner.isEmpty then throwError "the group field {field} holds no table"
        leaves := leaves ++ inner.map (·, some field)
      | none => leaves := leaves.push (field, none)
    for (field, group?) in leaves do
      let type ← inferType (← match group? with
        | some group => groupProjectionOf snapshotName group field
        | none => projectionOf snapshotName field)
      let held ← forallTelescope type fun _ body ↦ instantiateMVars body
      match (← whnf held).getAppFn.constName? with
      | some ``Rows =>
        let table := space ++ field
        unless env.contains table do throwError "no table {table} for the field {field}"
        auditTable snapshotName field table group?
        auditPrimaryKey table
        tables := tables.push table
      | some ``Index =>
        if group?.isSome then throwError "the index {field} is in a group of tables"
        indexes := indexes.push field
      | _ => throwError "the field {field} holds neither Rows nor an Index"
    let entries ← tables.mapM fun table ↦ mkAppM ``AnyTable.mk #[Lean.mkConst table]
    let expected ← mkListLit (mkApp (Lean.mkConst ``AnyTable) (Lean.mkConst snapshotName))
      entries.toList
    unless ← isDefEq (← mkAppM ``Schema.tables #[Lean.mkConst schemaName]) expected do
      throwError "{schemaName}.tables is not the tables of the Rows fields of {snapshotName} in \
        field order"
    let maintained ← tables.flatMapM fun table ↦ auditIndexes snapshotName table indexes
    for field in indexes do
      let count := (maintained.filter (· == field)).size
      unless count == 1 do
        throwError "the index {field} is maintained by {count} tables, not one"
    auditSubtypings schemaName space tables
    auditOwners schemaName space tables
    return (schemaName, snapshotName, tables)
  -- Each table's entry is proved from the tables from its position on (`positions.drop<k>`), each
  -- of those from the one before, so that no proof walks the list of tables from its start: one
  -- that did, for every table, took time in the square of their number (ten seconds of
  -- elaboration and kernel checking at three hundred tables).
  let schemaId := mkIdent (`_root_ ++ schemaName)
  let snapshotId := mkIdent (`_root_ ++ snapshotName)
  let positions := `_root_ ++ schemaName ++ `positions
  let from_ (k : Nat) : Ident := mkIdent (positions ++ .mkSimple s!"from{k}")
  let drop (k : Nat) : Ident := mkIdent (positions ++ .mkSimple s!"drop{k}")
  let tablesEq := mkIdent (positions ++ `tables_eq)
  let length := mkIdent (positions ++ `length)
  let count := tables.size
  -- exposed in a module, so that `schema_laws%` unfolds them in a module of its own
  let expose? : Option (TSyntax ``Parser.Term.attributes) ←
    if (← getEnv).header.isModule then some <$> `(Parser.Term.attributes| @[expose]) else pure none
  elabCommand (← `(command| $[$expose?:attributes]? noncomputable def $(from_ count) :
    List (AnyTable $snapshotId) := []))
  for (table, k) in tables.zipIdx.reverse do
    elabCommand (← `(command| $[$expose?:attributes]? noncomputable def $(from_ k) :
      List (AnyTable $snapshotId) := AnyTable.mk $(mkIdent (`_root_ ++ table)) :: $(from_ (k + 1))))
  -- These two walk the list of tables once, deeper than the default limit for schemas of a
  -- hundred tables and more.
  elabCommand (← `(command| set_option maxRecDepth 100000 in
    theorem $tablesEq:ident : ($schemaId).tables = $(from_ 0) := by rfl))
  elabCommand (← `(command| set_option maxRecDepth 100000 in
    theorem $length:ident : ($schemaId).tables.length = $(quote count) := by
      rw [$tablesEq:ident]; rfl))
  elabCommand (← `(command|
    theorem $(drop 0) : ($schemaId).tables.drop 0 = $(from_ 0) := $tablesEq:ident))
  for k in [1:count] do
    elabCommand (← `(command|
      theorem $(drop k) : ($schemaId).tables.drop $(quote k) = $(from_ k) :=
        List.tail_drop.symm.trans (congrArg List.tail $(drop (k - 1)))))
  for (table, position) in tables.zipIdx do
    let .str _ tableName := table | throwError "{table} is not a table name"
    let entry := mkIdent (`_root_ ++ schemaName ++ Name.mkSimple tableName)
    let k := quote position
    elabCommand (← `(command|
      instance $entry:ident : InSchema $schemaId $(mkIdent (`_root_ ++ table)) :=
        have bound : $k < ($schemaId).tables.length :=
          Nat.lt_of_lt_of_eq (by decide : $k < $(quote count)) (Eq.symm $length:ident)
        have rest : 0 < (($schemaId).tables.drop $k).length := by
          rw [List.length_drop]; exact Nat.sub_pos_of_lt bound
        ⟨⟨$k, bound⟩, (List.getElem_drop (i := $k) (j := 0) (h := rest)).symm.trans
          ((List.getElem_of_eq $(drop position) rest).trans (by rfl))⟩))
  -- Through the private constructor, which no term outside `Relational/Database.lean` can name.
  liftTermElabM do
    let name := schemaName ++ `instAudited
    let schema := Lean.mkConst schemaName
    let type ← mkAppM ``Audited #[schema]
    let value ← mkAppOptM auditedConstructor #[none, schema]
    addDecl <| .thmDecl { name, levelParams := [], type, value }
    addInstance name .global (eval_prio default)

end Relational
