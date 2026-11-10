module

public import Lean
public import Relational.Tables


-- all of it runs while `table%`, `table_rows%`, `table_defs%` and `declared_tables%` elaborate
public meta section

namespace Relational

open Lean Elab Command

/-! A schema's tables declared one at a time, each where its rows are.  `table% question :
QuestionRow (record) in Records` followed by `table%` clauses declares the table `question` of the
rows of type `QuestionRow`, with primary key `(record)`, held in a field `question` of the
structure `Records`; followed by `where` and a structure's fields (and `deriving`), it also
declares the structure `QuestionRow` of those fields there and then, deriving `DecidableEq` and
`Repr` unless a `deriving` clause says otherwise, so that a table and its rows are written once,
together.  When the command declares the row structure, a doc comment before
`table%` documents the structure and one after the header, before the clauses, documents the
table; a table of a row type declared elsewhere takes its doc comment before `table%`.

The structures that hold the tables and the tables themselves cannot be declared there: each
table's definition reads its field of the structure, which needs every table's field first.  So
`table%` declares the row structure at once and records the rest, and three commands use what it
recorded, in the order the tables were declared:
`table_rows% Records` declares the structure `Records` holding a `Rows key` for each table declared
in it (`table_rows% Snapshot extends Records` one that extends another, itself declared by
`table_rows%`), so a table is declared before the structure that holds it; `table_defs% Snapshot`
defines each table `f` of `Snapshot` and of the structures it extends as `table% Snapshot.f key
clauses` (and records them, so that `table_lemmas%` can state their simp lemmas in a module that
imports it); and the term `declared_tables% Snapshot` is the list of those tables in field order, as
`tables% [...]` writes it, for a schema.  A structure and those it extends are one schema's, so a
module may declare several schemas, one after another: a `table_defs%` or `declared_tables%` fails
while a table is declared in a structure that no `table_rows%` has declared, and `table_defs%` fails
for a structure whose tables it defined already.
The tables are not the structure's fields.  `table_rows%` puts them in groups of `groupSize`, in the
order they were declared, each group a structure of its own and a field of the structure, and
declares for each table `f` a reader `Records.f`, so that `rows.f` reads it as a field would (and a
structure that extends `Records` reads it the same way), and a writer `Records.set_f`, which rebuilds
the table's group and the structure: about `groupSize` plus the number of groups fields, where one
field per table would rebuild every table on every write.  A structure update `{ rows with f := v }`
does not elaborate, since `f` is no field; a table is written through its setter (`rows.set_f`,
or the table's `Table.set`).  Keep it so: the generated C of every setter of a flat structure holds
every table, and grows with the square of their number (Tables.c held 15 of its 25 MB of setters
at 253 tables).
The clauses are elaborated where `table_defs%` is, so a name they use may be declared after the
`table%` that uses it, as long as it is before `table_defs%`.  An error in a clause is reported at
the clause, one in a column it names at the column, and one in the definition as a whole (a primary
key that is not the one of the field's `Rows`) at the table's name; `table%` checks that the row
type has the primary key's columns, and an error in the key's type is reported at the key. -/

/-- A table declared by `table%`, for `table_rows%`, `table_defs%` and `declared_tables%`. -/
structure DeclaredTable where
  name : Ident
  row : Ident
  key : TSyntax `tableColumns
  holder : Ident
  doc? : Option (TSyntax ``Parser.Command.docComment)
  clauses : Array (TSyntax `tableClause)

/-- What `table%`, `table_rows%` and `table_defs%` did so far in the module: the tables declared, in
the order of their `table%`, the structures declared, each with the one it extends, and the
structures whose tables are defined. -/
structure DeclaredTables where
  tables : Array DeclaredTable := #[]
  structures : Array (Name × Option Name) := #[]
  defined : Array Name := #[]
  deriving Inhabited

/-- What `table%`, `table_rows%` and `table_defs%` did in the module being elaborated; not exported,
so that a module begins with none. -/
initialize declaredTables : EnvExtension DeclaredTables ← registerEnvExtension (pure {})

/-- A schema whose tables `table_defs%` defined, for `table_lemmas%` in a module that imports it:
the snapshot structure, and each table with the fields and setters of it that the snapshot and the
structures it extends declare, all by their full names. -/
structure DefinedSchema where
  snapshot : Name
  tables : Array (Name × Array Name)
  deriving Inhabited

/-- The schemas `table_defs%` defined, in this module and the ones it imports. -/
initialize definedSchemas : SimplePersistentEnvExtension DefinedSchema (Array DefinedSchema) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.flatten }

syntax (name := tableCommand) (docComment)? "table% " ident " : " ident tableColumns " in " ident
  (ppLine docComment)? (ppLine tableClause)*
  (" where" Parser.Command.structFields Parser.Command.optDeriving)? : command

syntax (name := tableRowsCommand) (docComment)? "table_rows% " ident (" extends " ident)? : command

syntax (name := tableDefsCommand) "table_defs% " ident : command

syntax (name := tableLemmasCommand) "table_lemmas% " ident " simp% " ident : command

syntax (name := declaredTablesTerm) "declared_tables% " ident : term

/-- The type of a table's `Rows` field: its rows of type `row`, keyed by the columns `key` names,
as `table%` reads its primary key, `(*)` the whole row; a column's projection takes the column's
position. -/
private def rowsType (row : Ident) (key : TSyntax `tableColumns) : MacroM Term := do
  let rowVariable := mkIdent `row
  match key with
  | `(tableColumns| (*)) => `(Rows (fun ($rowVariable : $row) ↦ $rowVariable))
  | `(tableColumns| ($column:ident)) => `(Rows $(mkIdentFrom column (row.getId ++ column.getId)))
  | `(tableColumns| ($columns,*)) =>
    let fields : Array Term := columns.getElems.map fun column ↦
      mkIdentFrom column (`row ++ column.getId)
    let some last := fields.back? | Macro.throwUnsupported
    let tuple ← fields.pop.foldrM (fun field rest ↦ `(($field, $rest))) last
    `(Rows (fun ($rowVariable : $row) ↦ $tuple))
  | _ => Macro.throwUnsupported

/-- The structure `holder` and those it extends, the one that extends no other first; fails at
`ref` unless `table_rows%` declared each. -/
private def schemaOf {m : Type → Type} [Monad m] [MonadRef m] [MonadError m]
    (state : DeclaredTables) (ref : Syntax) (holder : Name) : m (Array Name) := do
  let mut chain := #[]
  let mut current := holder
  repeat  -- principles: ignore[lean:while-loop] runs at elaboration, stops at the root structure; rewrite queued
    let some (_, parent?) := state.structures.find? (·.1 == current)
      | throwErrorAt ref "{current} is not a structure that table_rows% declared"
    chain := chain.push current
    match parent? with
    | some parent => current := parent
    | none => break
  return chain.reverse

/-- Fails unless `table_rows%` declared the structure of every table declared so far. -/
private def checkHolders {m : Type → Type} [Monad m] [MonadRef m] [MonadError m]
    (state : DeclaredTables) : m Unit := do
  for table in state.tables do
    unless state.structures.any (·.1 == table.holder.getId) do
      throwErrorAt table.holder
        "the table {table.name.getId} is in {table.holder.getId}, which no table_rows% has declared"

/-- The tables of the structures `schema`, in field order: those of a structure before those of one
that extends it, each structure's in the order they were declared. -/
private def tablesOf (state : DeclaredTables) (schema : Array Name) : Array DeclaredTable :=
  schema.flatMap fun holder ↦ state.tables.filter (·.holder.getId == holder)

@[command_elab tableCommand] def elabTable : CommandElab := fun stx ↦ do
  let doc? : Option (TSyntax ``Parser.Command.docComment) := stx[0].getOptional?.map (⟨·⟩)
  let name : Ident := ⟨stx[2]⟩
  let row : Ident := ⟨stx[4]⟩
  let key : TSyntax `tableColumns := ⟨stx[5]⟩
  let holder : Ident := ⟨stx[7]⟩
  let tableDoc? : Option (TSyntax ``Parser.Command.docComment) := stx[8].getOptional?.map (⟨·⟩)
  let clauses : Array (TSyntax `tableClause) := stx[9].getArgs.map (⟨·⟩)
  let state := declaredTables.getState (← getEnv)
  if state.tables.any (·.name.getId == name.getId) then
    throwErrorAt name "a table {name.getId} is declared already"
  if state.structures.any (·.1 == holder.getId) then
    throwErrorAt holder
      "{holder.getId} is declared already (table_rows%): a table in it is declared before it"
  -- an optional sequence is a node of its parts, or of none
  let tableDoc? ← match (if stx[10].getNumArgs == 0 then none else some stx[10]) with
    | some body =>
      let fields : TSyntax ``Parser.Command.structFields := ⟨body[1]⟩
      -- no `deriving` derives what a row's table needs, decidable equality (exposed, so that other
      -- modules decide it) and `Repr`
      -- an absent clause is the `optDeriving` node around an empty optional
      let deriving_ : TSyntax ``Parser.Command.optDeriving ← if body[2][0].isNone then
          `(Parser.Command.optDeriving| deriving @[expose] DecidableEq, Repr)
        else pure ⟨body[2]⟩
      elabCommand (← `(command| $[$doc?]? structure $row:ident where $fields:structFields $deriving_:optDeriving))
      pure tableDoc?
    | none =>
      if tableDoc?.isSome then
        throwErrorAt stx[8]
          "a table of a row type declared elsewhere takes its doc comment before table%"
      pure doc?
  -- the primary key's columns are the row type's, so that a wrong one is reported here, not where
  -- the table's structure is declared
  if let `(tableColumns| ($columns,*)) := key then
    let rowType ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo row
    let env ← getEnv
    unless isStructure env rowType do
      throwErrorAt row "{rowType} is not a structure"
    for column in columns.getElems do
      unless (getStructureFieldsFlattened env rowType).contains column.getId do
        throwErrorAt column "the row type {rowType} has no column {column.getId}"
  let table : DeclaredTable := { name, row, key, holder, doc? := tableDoc?, clauses }
  modifyEnv fun env ↦ declaredTables.modifyState env fun state ↦
    { state with tables := state.tables.push table }

/-- How many tables a group of a `table_rows%` structure holds: near the square root of their
number, so that a write rebuilds few fields both in its group and in the structure. -/
def groupSize : Nat := 16

@[command_elab tableRowsCommand] def elabTableRows : CommandElab := fun stx ↦ do
  let doc? : Option (TSyntax ``Parser.Command.docComment) := stx[0].getOptional?.map (⟨·⟩)
  let holder : Ident := ⟨stx[2]⟩
  let parent? : Option Ident := if stx[3].getNumArgs == 0 then none else some ⟨stx[3][1]⟩
  let state := declaredTables.getState (← getEnv)
  if state.structures.any (·.1 == holder.getId) then
    throwErrorAt holder "{holder.getId} is declared already"
  if let some parent := parent? then
    discard <| schemaOf state parent parent.getId
  let tables := state.tables.filter (·.holder.getId == holder.getId)
  if tables.isEmpty then
    throwErrorAt holder "no table is declared in {holder.getId}"
  -- the tables in groups of `groupSize`, in the order they were declared: a write rebuilds its
  -- table's group and the structure, not every table
  let typed ← tables.mapM fun table ↦ do
    return (table, ← withRef table.key <| liftMacroM (rowsType table.row table.key))
  let groups := (List.range ((typed.size + groupSize - 1) / groupSize)).toArray.map fun k ↦
    typed.extract (k * groupSize) ((k + 1) * groupSize)
  let .str _ last := holder.getId | throwErrorAt holder "{holder.getId} does not end in a name"
  let groupField (k : Nat) : Ident := mkIdent (.mkSimple s!"{last}Group{k}")
  let groupType (k : Nat) : Ident := mkIdent (holder.getId ++ .mkSimple s!"Group{k}")
  for (group, k) in groups.zipIdx do
    let fields ← group.mapM fun (table, type) ↦
      `(Parser.Command.structSimpleBinder| $(table.name):ident : $type := {})
    elabCommand (← `(command| structure $(groupType k):ident where $[$fields]*))
  let groupFields ← (List.range groups.size).toArray.mapM fun k ↦
    `(Parser.Command.structSimpleBinder| $(groupField k):ident : $(groupType k):ident := {})
  match parent? with
  | some parent =>
    elabCommand (← `(command| $[$doc?]? structure $holder:ident extends $parent:ident where
      $[$groupFields]*))
  | none => elabCommand (← `(command| $[$doc?]? structure $holder:ident where $[$groupFields]*))
  -- each table read and written through its group, under its own name
  let s := mkIdent `s
  let v := mkIdent `v
  for (group, k) in groups.zipIdx do
    for (table, type) in group do
      let getter := mkIdent (holder.getId ++ table.name.getId)
      let setter := mkIdent (holder.getId ++ .mkSimple s!"set_{table.name.getId}")
      let g := groupField k
      -- exposed, so that other modules unfold them (the read-back proofs' `simp`): their bodies are
      -- the structure's layout, which importers see anyway
      elabCommand (← `(command| @[expose, reducible] def $getter:ident ($s : $holder) : $type :=
        $s.$g:ident.$(table.name):ident))
      elabCommand (← `(command| @[expose] def $setter:ident ($s : $holder) ($v : $type) : $holder :=
        { $s with $g:ident := { $s.$g:ident with $(table.name):ident := $v } }))
  -- and a structure that extends another writes the other's tables through the other's setters
  if let some parent := parent? then
    let parentName := parent.getId
    let .str _ parentLast := parentName | throwErrorAt parent "{parentName} does not end in a name"
    let toParent := mkIdent (.mkSimple s!"to{parentLast}")
    let chain ← schemaOf state parent parentName
    for table in tablesOf state chain do
      let type ← withRef table.key <| liftMacroM (rowsType table.row table.key)
      let setter := mkIdent (holder.getId ++ .mkSimple s!"set_{table.name.getId}")
      let parentSetter := mkIdent (table.holder.getId ++ .mkSimple s!"set_{table.name.getId}")
      let viaParent ← if table.holder.getId == parentName then
          `($parentSetter ($s).$toParent:ident $v)
        else
          `($(mkIdent (parentName ++ .mkSimple s!"set_{table.name.getId}")) ($s).$toParent:ident $v)
      elabCommand (← `(command| @[expose] def $setter:ident ($s : $holder) ($v : $type) : $holder :=
        { $s with $toParent:ident := $viaParent }))
  modifyEnv fun env ↦ declaredTables.modifyState env fun state ↦
    { state with structures := state.structures.push (holder.getId, parent?.map (·.getId)) }

@[command_elab tableDefsCommand] def elabTableDefs : CommandElab := fun stx ↦ do
  let snapshot : Ident := ⟨stx[1]⟩
  let state := declaredTables.getState (← getEnv)
  checkHolders state
  let schema ← schemaOf state snapshot snapshot.getId
  if let some holder := schema.find? state.defined.contains then
    throwErrorAt snapshot "the tables of {holder} are defined already"
  let namespace_ ← getCurrNamespace
  let mut defined := #[]
  for table in state.tables.filter (schema.contains ·.holder.getId) do
    let field := mkIdent (snapshot.getId ++ table.name.getId)
    let clauses := table.clauses
    let setter := mkIdent (snapshot.getId ++ .mkSimple s!"set_{table.name.getId}")
    withRef table.name do
      elabCommand (← `(command| $[$(table.doc?)]? @[expose] def $(table.name):ident :=
        table% $field:ident $(table.key):tableColumns set% $setter:ident $clauses:tableClause*))
    -- a structure is recorded by the name `table_rows%` was given, which the current namespace
    -- may qualify
    let name := table.name.getId
    let env ← getEnv
    let accessors := (schema.flatMap fun holder ↦
      #[holder ++ name, holder ++ .mkSimple s!"set_{name}"]).filterMap fun accessor ↦
        [namespace_ ++ accessor, accessor].find? env.contains
    defined := defined.push (namespace_ ++ name, accessors)
  let snapshotName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo snapshot
  modifyEnv fun env ↦ definedSchemas.addEntry
    (declaredTables.modifyState env fun state ↦ { state with defined := state.defined ++ schema })
    { snapshot := snapshotName, tables := defined }

/-- `table_lemmas% Snapshot simp% s` adds to the simp set `s`, for each table of the schema whose
snapshot is `Snapshot` (defined by `table_defs%` in an imported module), the lemmas `t.rows_def`
and `t.set_def`, which state the table's `rows` and `set` as the snapshot's own field and setter,
and the fields and setters of `t` that the structures declare, so that `simp only [s]` reads a
table through a run of updates one at a time, without unfolding the table's definition.  It is a
command of its own, in the module of the proofs that use the simp set, so that the schema's module,
which every module that reads a table imports, does not elaborate them. -/
@[command_elab tableLemmasCommand] def elabTableLemmas : CommandElab := fun stx ↦ do
  let snapshot : Ident := ⟨stx[1]⟩
  let simpSet : Ident := ⟨stx[3]⟩
  let snapshotName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo snapshot
  let some defined := (definedSchemas.getState (← getEnv)).find? (·.snapshot == snapshotName)
    | throwErrorAt snapshot "no table_defs% defined the tables of {snapshotName}"
  let s := mkIdent `s
  let snapshotType := mkCIdentFrom snapshot snapshotName
  let mut names := #[]
  for (table, accessors) in defined.tables do
    let .str _ last := table | throwErrorAt snapshot "the table {table} has no simple name"
    let rowsDef := table ++ `rows_def
    let setDef := table ++ `set_def
    -- `t.rows` is the field access `Table.rows t`, written as one name
    let rows := mkIdent (table ++ `rows)
    let set := mkIdent (table ++ `set)
    let read := mkIdent (`s ++ .mkSimple last)
    let setter := mkCIdentFrom snapshot (snapshotName ++ .mkSimple s!"set_{last}")
    -- proved by the tactic, not the term `rfl`, so that the lemmas export no table's body
    elabCommand (← `(command| theorem $(mkIdent (`_root_ ++ rowsDef)):ident :
      $rows = fun ($s : $snapshotType) ↦ $read := by rfl))
    elabCommand (← `(command| theorem $(mkIdent (`_root_ ++ setDef)):ident :
      $set = $setter := by rfl))
    names := names ++ #[rowsDef, setDef] ++ accessors
  -- a simp set's attribute has a parser of its own, so the command is read from its text, each name
  -- escaped as it would be written
  let written := names.map fun name ↦ (`_root_ ++ name).toString (escape := true)
  let text := s!"attribute [{simpSet.getId.toString (escape := true)}] {" ".intercalate written.toList}"
  match Parser.runParserCategory (← getEnv) `command text with
  | .ok command => elabCommand command
  | .error message => throwErrorAt simpSet "table_lemmas%: {message}"

@[term_elab declaredTablesTerm] def elabDeclaredTables : Term.TermElab := fun stx expectedType? ↦ do
  let snapshot : Ident := ⟨stx[1]⟩
  let state := declaredTables.getState (← getEnv)
  checkHolders state
  let names := (tablesOf state (← schemaOf state snapshot snapshot.getId)).map (·.name)
  Term.elabTerm (← `(tables% [$names,*])) expectedType?

end Relational
