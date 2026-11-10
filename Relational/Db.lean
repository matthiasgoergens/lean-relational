module

public import Relational.Incremental

public section

namespace Relational

/-! `Db`, a snapshot that satisfies its schema, with the indexes the incremental check probes.
`Db.load` checks a snapshot read from a store, every row of it.  `Db.append` adds the rows of a
delta, each to a table of the schema, and decides from the rows the delta adds alone whether the
result is valid (`Schema.Accepts`), probing the database's indexes at one key per new row and
constraint; it requires the laws of the schema's readers and writers (`Schema.Wiring`) and the
table each constraint reads (`Schema.Coherent`), both generated per schema, so that no check of the
whole result is needed.  `Schema.accepts_iff` states that on a valid database it accepts exactly
what the whole-result check would.  The old database stays usable: the tables share all but the
changed paths of their trees.  The `Db` type itself records no history, and `load` is public, so a
`Db` may come from anywhere.  What the types guarantee is in `Db.Grown db`, a database grown from
`db`, which only `append` makes and `Grown.refl` and `Grown.trans` compose: a step typed
`(db : Db schema) → Except Refusal db.Grown` can only append to `db`, any number of times, and
returns a database that keeps every row of it. -/

/-- A snapshot that satisfies the schema's constraints, with an index per further unique key and
per mandatory participation of each table, which agree with its rows.  The constructor is private,
so every database is valid: `load` makes one from a snapshot read from a store, and `append` from
another database.  Since `load` is public, the type does not say where a database came from;
`Grown` says that one was appended to another.

These indexes are not the tables' own (`index%`, `Table.indexes`), and neither can stand in for
the other.  A table's own indexes are fields of the caller's snapshot type, declared for the
caller's queries and kept by `Insert.apply` through the table's functions.  The indexes here are
typed by the constraint they serve (an `Index` by the unique key's or the participation's column),
one for every such constraint whatever the caller declares, and kept outside the snapshot.
Probing the tables' own indexes instead would oblige every schema to declare a snapshot field for
each further unique key and mandatory participation, and to prove for each that its column is the
constraint's; keeping the tables' own indexes here would take them out of the snapshot that the
caller reads.  Where a caller declares an index by the column of a unique key or participation,
that column is indexed twice: O(n) more memory, and one more O(log n) insertion per row. -/
structure Db {Snapshot : Type} (schema : Schema Snapshot) where
  private mk ::
  rows : Snapshot
  valid : schema.Valid rows
  indexes : schema.Indexes
  agree : schema.IndexesAgree rows indexes

namespace Db

variable {Snapshot : Type} {schema : Schema Snapshot}

/-- The database of a snapshot read from a store, or the first constraint it violates, with its
indexes built from its rows.  A caller starts each operation from the store it reads; within an
operation, the database grows only by `append`. -/
def load (schema : Schema Snapshot) [Audited schema] (rows : Snapshot) :
    Except Violation (Db schema) :=
  match found : schema.violation? rows with
  | some violation => .error violation
  | none => .ok ⟨rows, Schema.valid_of_violation?_eq_none found, Schema.Indexes.ofSnapshot schema rows,
      Schema.indexesAgree_ofSnapshot rows⟩

theorem load_rows [Audited schema] {rows : Snapshot} {db : Db schema}
    (accepted : load schema rows = .ok db) :
    db.rows = rows := by
  unfold load at accepted
  split at accepted
  · cases accepted
  · cases accepted
    rfl

/-- What `load` refuses violates the schema as it says. -/
theorem load_refused [Audited schema] {rows : Snapshot} {violation : Violation}
    (refused : load schema rows = .error violation) : schema.Violated rows violation := by
  unfold load at refused
  split at refused
  · rename_i found
    cases refused
    exact Schema.violation?_sound found
  · cases refused

/-- A database grown from `db` by appending to it, any number of times, with the proof that every
table keeps all of `db`'s rows.  The constructor is private: `append` makes one (through
`GrownBy.toGrown`), and `refl` and `trans` compose them, so a step typed
`(db : Db schema) → Except Refusal db.Grown` cannot return a database that `load` made. -/
structure Grown (db : Db schema) where
  private mk ::
  next : Db schema
  kept : schema.Extends db.rows next.rows

/-- The database `db` grown by the one delta `delta`, as `append` returns it: every table holds
exactly its rows in `db` and the delta's rows for it.  The constructor is private. -/
structure GrownBy (db : Db schema) (delta : List (Insert schema)) where
  private mk ::
  next : Db schema
  appended : schema.Appended db.rows delta next.rows

/-- The database grown by one delta, as grown from `db`. -/
def GrownBy.toGrown {db : Db schema} {delta : List (Insert schema)} (grown : db.GrownBy delta) :
    db.Grown :=
  ⟨grown.next, grown.appended.extends⟩

/-- `db` itself, grown by nothing. -/
def Grown.refl (db : Db schema) : db.Grown := ⟨db, Schema.Extends.refl db.rows⟩

/-- A database grown from one grown from `db`, as grown from `db`. -/
def Grown.trans {db : Db schema} (first : db.Grown) (second : first.next.Grown) : db.Grown :=
  ⟨second.next, first.kept.trans second.kept⟩

/-- A row of a table of the schema that `db` has, a database grown from it has. -/
theorem Grown.mem {Row Key : Type} [DecidableEq Row] [TreeOrd Key] {key : Row → Key}
    {table : Table Snapshot key} [entry : InSchema schema table] {db : Db schema} (grown : db.Grown)
    {row : Row} (member : row ∈ table.rows db.rows) : row ∈ table.rows grown.next.rows := by
  have listed : (table : AnyTable Snapshot) ∈ schema.tables := by
    rw [← entry.listed, Fin.getElem_fin]
    exact List.getElem_mem entry.position.isLt
  exact grown.kept _ listed row member

/-- A primary key of a table of the schema that `db` has, a database grown from it has. -/
theorem Grown.contains {Row Key : Type} [DecidableEq Row] [TreeOrd Key] {key : Row → Key}
    {table : Table Snapshot key} [InSchema schema table] {db : Db schema} (grown : db.Grown)
    {primary : Key} (present : (table.rows db.rows).contains primary = true) :
    (table.rows grown.next.rows).contains primary = true := by
  obtain ⟨row, member, same⟩ := Rows.contains_iff.mp present
  exact Rows.contains_iff.mpr ⟨row, grown.mem member, same⟩

/-- The grown snapshot and its indexes, for a delta the grown snapshot accepts, as a database. -/
private def grownOf [schema.Wiring] [schema.Coherent] (db : Db schema) (delta : List (Insert schema))
    (grown : Snapshot × schema.Indexes) (same : schema.grow db.rows db.indexes delta = grown)
    (accepts : schema.Accepts db.rows delta) : db.GrownBy delta :=
  ⟨⟨grown.1, by rw [← same, Schema.grow_fst]; exact Schema.valid_of_accepts db.valid accepts, grown.2,
      by rw [← same]; exact Schema.indexesAgree_grow delta db.agree⟩,
    by show schema.Appended db.rows delta grown.1
       rw [← same, Schema.grow_fst]
       exact Schema.appended_of_keysAgree accepts.1⟩

/-- The database with the rows of `delta` added, from a proof that it accepts them: no runtime
check, in O(d log n) time for d rows of the delta and n of the database. -/
def appendProved [Audited schema] [schema.Wiring] [schema.Coherent] (db : Db schema)
    (delta : List (Insert schema)) (accepts : schema.Accepts db.rows delta) : db.GrownBy delta :=
  grownOf db delta (schema.grow db.rows db.indexes delta) rfl accepts

/-- Why the database refuses `delta`, if it does: `Schema.refusal?` on the grown snapshot and its
indexes. -/
def refusal? [schema.Coherent] (db : Db schema) (delta : List (Insert schema)) : Option Refusal :=
  schema.refusal? db.rows delta (schema.grow db.rows db.indexes delta).1
    (schema.grow db.rows db.indexes delta).2

theorem refusal?_eq_none [schema.Wiring] [schema.Coherent] {db : Db schema} {delta : List (Insert schema)} :
    db.refusal? delta = none ↔ schema.Accepts db.rows delta := by
  have agree := Schema.indexesAgree_grow delta db.agree
  unfold refusal?
  rw [Schema.grow_fst] at agree ⊢
  exact Schema.refusal?_eq_none agree

theorem refusal?_sound [schema.Wiring] [schema.Coherent] {db : Db schema} {delta : List (Insert schema)}
    {refusal : Refusal} (found : db.refusal? delta = some refusal) : schema.Refuses db.rows delta refusal := by
  have agree := Schema.indexesAgree_grow delta db.agree
  unfold refusal? at found
  rw [Schema.grow_fst] at agree found
  exact Schema.refusal?_sound agree found

/-- `Accepts`, decided from the database's indexes. -/
def decideAccepts [schema.Wiring] [schema.Coherent] (db : Db schema) (delta : List (Insert schema)) :
    Decidable (schema.Accepts db.rows delta) :=
  decidable_of_iff _ (refusal?_eq_none (db := db) (delta := delta))

/-- The database with the rows of `delta` added, each to its table and the table's indexes, if
the delta's rows keep every constraint (`Schema.Accepts`, decided from the rows the delta adds and
the database's indexes); the result type states that every table holds exactly its old rows and
the delta's rows for it (`Appended`, from which `Appended.extends` and `Appended.added` follow).
An appended row that a table already has changes nothing.  Otherwise the first refusal, in this
order: a row with the primary key of a different row, of the table or of the delta; a further
unique key, a foreign key, a mandatory participation, a subtype member or a covering subtyping
that a new row breaks.  In O(d log (n + d)) time for d rows of the delta and n of the database,
besides a pass over the schema's tables and constraints. -/
def append [Audited schema] [schema.Wiring] [schema.Coherent] (db : Db schema)
    (delta : List (Insert schema)) : Except Refusal (db.GrownBy delta) :=
  let grown := schema.grow db.rows db.indexes delta
  match found : schema.refusal? db.rows delta grown.1 grown.2 with
  | some refusal => .error refusal
  | none => .ok (grownOf db delta grown rfl (refusal?_eq_none.mp found))

/-- The database grown from `db` with `delta` appended to it, for a step that appends several
deltas in turn. -/
def Grown.append [Audited schema] [schema.Wiring] [schema.Coherent] {db : Db schema} (grown : db.Grown)
    (delta : List (Insert schema)) : Except Refusal db.Grown := do
  let step ← grown.next.append delta
  return grown.trans step.toGrown

/-- What `append` refuses is refused for the reason it gives: a conflict of primary keys, or a
violation of the database with the delta applied. -/
theorem append_refused [Audited schema] [schema.Wiring] [schema.Coherent] {db : Db schema}
    {delta : List (Insert schema)} {refusal : Refusal}
    (refused : db.append delta = .error refusal) : schema.Refuses db.rows delta refusal := by
  unfold append at refused
  dsimp only at refused
  split at refused
  · rename_i found
    cases refused
    exact refusal?_sound found
  · cases refused

/-- What `append` accepts is the old database with exactly the delta's rows added. -/
theorem append_accepted [Audited schema] [schema.Wiring] [schema.Coherent] {db : Db schema}
    {delta : List (Insert schema)} {grown : db.GrownBy delta} (accepted : db.append delta = .ok grown) :
    grown.next.rows = schema.applied db.rows delta ∧ schema.Extends db.rows grown.next.rows := by
  refine ⟨?_, grown.appended.extends⟩
  unfold append at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · cases accepted
    exact Schema.grow_fst delta db.rows db.indexes

/-- `append` succeeds exactly on the deltas that `Accepts` holds of, so that a caller who proves
`Accepts` knows that `append` will not refuse, and one who sees a refusal knows that `Accepts`
fails. -/
theorem append_isOk [Audited schema] [schema.Wiring] [schema.Coherent] {db : Db schema}
    {delta : List (Insert schema)} : (db.append delta).isOk = true ↔ schema.Accepts db.rows delta := by
  rw [← refusal?_eq_none]
  unfold append refusal?
  dsimp only
  split
  · rename_i found
    simp [found, Except.isOk, Except.toBool]
  · rename_i found
    simp [found, Except.isOk, Except.toBool]

end Db

end Relational
