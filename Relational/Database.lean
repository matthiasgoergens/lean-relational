module

public import Relational.Tables


public section

namespace Relational

/-! A database's schema over a snapshot structure: its tables and subtypings, `Valid` for its
constraints, `violation?`, which decides it and names the table and the constraint that fails, and
the inserts of a delta, with `Appended`, which states that every table holds exactly its old rows
and the delta's rows for it (and so implies `Extends`: no row is lost), and the refusals of an
append.  `Db` (`Relational.Db`) is a snapshot that satisfies its schema; `Audited` records that a
schema passed the schema audit, which `Db.load` and `Db.append` require.  `Schema.Frozen`
adds, for two snapshots, that no table has a new row of an owner that the earlier one has, as
each table declares its owners; `Schema.thaw?` decides it and names the table, the row and its
owner. -/


/-- A snapshot's tables, in field order, and its subtypings. -/
structure Schema (Snapshot : Type) where
  tables : List (AnyTable Snapshot)
  subtypings : List (Subtyping Snapshot) := []

/-- Why a snapshot violates its schema, naming the table and the constraint. -/
inductive Violation where
  /-- Two rows of `table` share the value of the further unique key `key`. -/
  | duplicate (table key : String)
  /-- A row of `table` has a value of `column` that matches no parent row. -/
  | dangling (table column : String)
  /-- A row of `table` has a value of `column` that matches a parent row it may not refer to: of
  a kind or fact that the foreign key's restriction does not allow for the row. -/
  | wrongKind (table column : String)
  /-- A row of the subtype table `member` of `supertype` has a key that no row of the supertype
  has. -/
  | orphan (supertype member : String)
  /-- A row of the subtype table `member` of `supertype` has the key of a supertype row whose
  discriminating column has none of the member's values. -/
  | wrongFact (supertype member : String)
  /-- A parent row that the mandatory participation through `column` covers has no row of
  `table` that refers to it. -/
  | missing (table column : String)
  /-- The subtype tables `first` and `second` of `supertype`, two distinct members of one
  subtyping, share a key. -/
  | overlap (supertype first second : String)
  /-- A row of `supertype` in the scope of the covering or exhaustive subtyping with the subtype
  tables `members` is in none of them. -/
  | uncovered (supertype : String) (members : List String)
  /-- The index `index` of `table` disagrees with the table's rows. -/
  | staleIndex (table index : String)
  deriving @[expose] DecidableEq, Repr

namespace Schema

variable {Snapshot : Type} (schema : Schema Snapshot)

/-- Every table's further unique keys; primary keys are unique by construction. -/
@[expose] def Keys (rows : Snapshot) : Prop := ∀ entry ∈ schema.tables, entry.table.Keyed rows

/-- Every table's foreign keys, including those restricted to some kinds of parent row. -/
@[expose] def ForeignKeys (rows : Snapshot) : Prop := ∀ entry ∈ schema.tables, entry.table.Referenced rows

/-- Every row of a subtype table has the key of a supertype row of one of the subtype's facts. -/
@[expose] def Typed (rows : Snapshot) : Prop := ∀ subtyping ∈ schema.subtypings, subtyping.Typed rows

/-- Every table's mandatory participations. -/
@[expose] def Participations (rows : Snapshot) : Prop :=
  ∀ entry ∈ schema.tables, entry.table.Participates rows

/-- No two subtype tables of a supertype share a key. -/
@[expose] def Disjoint (rows : Snapshot) : Prop :=
  ∀ subtyping ∈ schema.subtypings, subtyping.Disjoint rows

/-- Every supertype row in the scope of a covering or exhaustive subtyping is of one of its
subtypes. -/
@[expose] def Covered (rows : Snapshot) : Prop := ∀ subtyping ∈ schema.subtypings, subtyping.Covered rows

/-- Every index agrees with its table. -/
@[expose] def Indexed (rows : Snapshot) : Prop := ∀ entry ∈ schema.tables, entry.table.Indexed rows

@[expose] def Valid (rows : Snapshot) : Prop :=
  schema.Keys rows ∧ schema.ForeignKeys rows ∧ schema.Typed rows ∧ schema.Participations rows ∧
    schema.Disjoint rows ∧ schema.Covered rows ∧ schema.Indexed rows

/-- Every table of `next` has every row of the same table of `previous`. -/
@[expose] def Extends (previous next : Snapshot) : Prop :=
  ∀ entry ∈ schema.tables, (entry.table.rows previous).Included (entry.table.rows next)

theorem Extends.refl {schema : Schema Snapshot} (rows : Snapshot) : schema.Extends rows rows :=
  fun _ _ _ member ↦ member

theorem Extends.trans {schema : Schema Snapshot} {first second third : Snapshot}
    (earlier : schema.Extends first second) (later : schema.Extends second third) :
    schema.Extends first third :=
  fun entry member row inFirst ↦ later entry member row (earlier entry member row inFirst)

instance (rows : Snapshot) : Decidable (schema.Keys rows) := inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance (rows : Snapshot) : Decidable (schema.ForeignKeys rows) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance (rows : Snapshot) : Decidable (schema.Typed rows) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance (rows : Snapshot) : Decidable (schema.Participations rows) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance (rows : Snapshot) : Decidable (schema.Disjoint rows) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance (rows : Snapshot) : Decidable (schema.Covered rows) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance (rows : Snapshot) : Decidable (schema.Indexed rows) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance (rows : Snapshot) : Decidable (schema.Valid rows) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (previous next : Snapshot) : Decidable (schema.Extends previous next) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The first table and further unique key that two rows share. -/
def firstDuplicate? (rows : Snapshot) : Option Violation :=
  schema.tables.findSome? fun entry ↦
    (entry.table.duplicate? rows).map (.duplicate entry.table.name ·)

/-- The first table and column with a value that matches no parent row it may refer to:
`dangling` if a row's value of the column matches no parent row at all, and otherwise
`wrongKind`, for a row whose value matches a parent row that the foreign key's restriction does
not allow for it. -/
def firstUnmatched? (rows : Snapshot) : Option Violation :=
  schema.tables.findSome? fun entry ↦ (entry.table.unmatched? rows).map fun (foreign, present) ↦
    if present then .wrongKind entry.table.name foreign.column
    else .dangling entry.table.name foreign.column

/-- The first subtyping and subtype table with a row whose key is no supertype row's (`orphan`) or
a supertype row's of another fact (`wrongFact`). -/
def firstMisfit? (rows : Snapshot) : Option Violation :=
  schema.subtypings.findSome? fun subtyping ↦ (subtyping.firstMisfit rows).map fun (member, wrong) ↦
    if wrong then .wrongFact subtyping.name member else .orphan subtyping.name member

/-- The first table and column of a mandatory participation that a parent row lacks. -/
def firstMissing? (rows : Snapshot) : Option Violation :=
  schema.tables.findSome? fun entry ↦ (entry.table.unmet? rows).map (.missing entry.table.name ·)

/-- The first supertype and pair of its subtype tables that share a key. -/
def firstOverlap? (rows : Snapshot) : Option Violation :=
  schema.subtypings.findSome? fun subtyping ↦
    (Subtyping.firstOverlap rows subtyping.members).map fun (first, second) ↦
      .overlap subtyping.name first second

/-- The first covering or exhaustive subtyping with a supertype row in scope that is of no
subtype. -/
def firstUncovered? (rows : Snapshot) : Option Violation :=
  (schema.subtypings.find? fun subtyping ↦
      !subtyping.coveredBy rows).map fun subtyping ↦
    .uncovered subtyping.name (subtyping.members.map (·.name))

/-- The first table and index that disagree. -/
def firstStale? (rows : Snapshot) : Option Violation :=
  schema.tables.findSome? fun entry ↦
    (entry.table.unindexed? rows).map (.staleIndex entry.table.name ·)

/-- The first constraint of the schema that `rows` violates. -/
def violation? (rows : Snapshot) : Option Violation :=
  (schema.firstDuplicate? rows).or <| (schema.firstUnmatched? rows).or <|
    (schema.firstMisfit? rows).or <| (schema.firstMissing? rows).or <|
      (schema.firstOverlap? rows).or <| (schema.firstUncovered? rows).or (schema.firstStale? rows)

/-- What a violation says about a snapshot. -/
@[expose] def Violated (rows : Snapshot) : Violation → Prop
  | .duplicate table key => ∃ entry ∈ schema.tables, entry.table.name = table ∧
      entry.table.KeyShared rows key
  | .dangling table column => ∃ entry ∈ schema.tables, entry.table.name = table ∧
      entry.table.ColumnDangles rows column
  | .wrongKind table column => ∃ entry ∈ schema.tables, entry.table.name = table ∧
      entry.table.ColumnWrongKind rows column
  | .orphan supertype member => ∃ subtyping ∈ schema.subtypings, subtyping.name = supertype ∧
      subtyping.Orphaned rows member
  | .wrongFact supertype member => ∃ subtyping ∈ schema.subtypings, subtyping.name = supertype ∧
      subtyping.Misfiled rows member
  | .missing table column => ∃ entry ∈ schema.tables, entry.table.name = table ∧
      entry.table.ColumnMissing rows column
  | .overlap supertype first second => ∃ subtyping ∈ schema.subtypings,
      subtyping.name = supertype ∧ ∃ member other, [member, other].Sublist subtyping.members ∧
        member.name = first ∧ other.name = second ∧ ¬ Subtyping.Apart member other rows
  | .uncovered supertype members => ∃ subtyping ∈ schema.subtypings,
      subtyping.name = supertype ∧ subtyping.members.map (·.name) = members ∧
        ∃ primary ∈ subtyping.covered rows, ∀ member ∈ subtyping.members,
          primary ∉ member.keys rows
  | .staleIndex table index => ∃ entry ∈ schema.tables, entry.table.name = table ∧
      entry.table.IndexStale rows index

variable {schema}

/-- `violation?` reports nothing exactly for a valid snapshot. -/
theorem violation?_eq_none {rows : Snapshot} : schema.violation? rows = none ↔ schema.Valid rows := by
  simp only [violation?, Option.or_eq_none_iff, firstDuplicate?, firstUnmatched?, firstMisfit?,
    firstMissing?, firstOverlap?, firstUncovered?, firstStale?, List.findSome?_eq_none_iff,
    Option.map_eq_none_iff, List.find?_eq_none, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    Classical.not_not, Table.duplicate?_eq_none, Table.unmatched?_eq_none, Table.unmet?_eq_none,
    Subtyping.firstMisfit_eq_none, Subtyping.firstOverlap_eq_none, Subtyping.coveredBy_iff,
    Table.unindexed?_eq_none, Valid, Keys, ForeignKeys, Typed, Participations, Disjoint, Covered,
    Indexed, Subtyping.Disjoint]

/-- A snapshot each of whose tables has no rows has no two rows that share a further unique key. -/
theorem keys_of_empty {rows : Snapshot} (empty : ∀ entry ∈ schema.tables, ∀ row, row ∉ entry.table.rows rows) :
    schema.Keys rows :=
  fun entry member _ _ ↦ Relation.keyed_iff_mem.mpr ⟨Rows.toRelation_distinct,
    fun row inside ↦ absurd (Rows.mem_toRelation.mp inside) (empty entry member row)⟩

/-- `firstDuplicate?` reports nothing exactly where every further unique key holds. -/
theorem firstDuplicate?_eq_none {rows : Snapshot} : schema.firstDuplicate? rows = none ↔ schema.Keys rows := by
  simp only [firstDuplicate?, List.findSome?_eq_none_iff, Option.map_eq_none_iff, Table.duplicate?_eq_none, Keys]

theorem valid_of_violation?_eq_none {rows : Snapshot} (none : schema.violation? rows = none) :
    schema.Valid rows :=
  violation?_eq_none.mp none

private theorem firstDuplicate?_sound {rows : Snapshot} {violation : Violation}
    (found : schema.firstDuplicate? rows = some violation) : schema.Violated rows violation := by
  obtain ⟨entry, member, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨key, duplicate, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨entry, member, rfl, Table.duplicate?_eq_some duplicate⟩

private theorem firstUnmatched?_sound {rows : Snapshot} {violation : Violation}
    (found : schema.firstUnmatched? rows = some violation) : schema.Violated rows violation := by
  obtain ⟨entry, member, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨⟨foreign, present⟩, unmatched, rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨dangles, wrongKind⟩ := Table.unmatched?_eq_some unmatched
  cases present
  · exact ⟨entry, member, rfl, dangles rfl⟩
  · exact ⟨entry, member, rfl, wrongKind rfl⟩

private theorem firstMisfit?_sound {rows : Snapshot} {violation : Violation}
    (found : schema.firstMisfit? rows = some violation) : schema.Violated rows violation := by
  obtain ⟨subtyping, member, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨⟨name, wrong⟩, misfit, rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨orphan, misfiled⟩ := Subtyping.firstMisfit_eq_some misfit
  cases wrong
  · exact ⟨subtyping, member, rfl, orphan rfl⟩
  · exact ⟨subtyping, member, rfl, misfiled rfl⟩

private theorem firstMissing?_sound {rows : Snapshot} {violation : Violation}
    (found : schema.firstMissing? rows = some violation) : schema.Violated rows violation := by
  obtain ⟨entry, member, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨column, unmet, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨entry, member, rfl, Table.unmet?_eq_some unmet⟩

private theorem firstOverlap?_sound {rows : Snapshot} {violation : Violation}
    (found : schema.firstOverlap? rows = some violation) : schema.Violated rows violation := by
  obtain ⟨subtyping, member, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨⟨first, second⟩, overlap, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨subtyping, member, rfl, Subtyping.firstOverlap_eq_some overlap⟩

private theorem firstUncovered?_sound {rows : Snapshot} {violation : Violation}
    (found : schema.firstUncovered? rows = some violation) : schema.Violated rows violation := by
  obtain ⟨subtyping, first, rfl⟩ := Option.map_eq_some_iff.mp found
  have failing := List.find?_some first
  simp only [Bool.not_eq_true'] at failing
  have uncovered : ¬ ∀ primary ∈ subtyping.covered rows, ∃ member ∈ subtyping.members,
      primary ∈ member.keys rows :=
    fun covered ↦ by simp [Subtyping.coveredBy_iff.mpr covered] at failing
  simp only [Classical.not_forall, not_exists, not_and] at uncovered
  obtain ⟨primary, inScope, none⟩ := uncovered
  exact ⟨subtyping, List.mem_of_find?_eq_some first, rfl, rfl, primary, inScope, none⟩

private theorem firstStale?_sound {rows : Snapshot} {violation : Violation}
    (found : schema.firstStale? rows = some violation) : schema.Violated rows violation := by
  obtain ⟨entry, member, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨index, stale, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨entry, member, rfl, Table.unindexed?_eq_some stale⟩

/-- A violation that `violation?` reports holds of the snapshot. -/
theorem violation?_sound {rows : Snapshot} {violation : Violation}
    (found : schema.violation? rows = some violation) : schema.Violated rows violation := by
  simp only [violation?, Option.or_eq_some_iff] at found
  rcases found with duplicate | ⟨_, unmatched | ⟨_, misfit | ⟨_, missing | ⟨_, overlap |
    ⟨_, uncovered | ⟨_, stale⟩⟩⟩⟩⟩⟩
  · exact firstDuplicate?_sound duplicate
  · exact firstUnmatched?_sound unmatched
  · exact firstMisfit?_sound misfit
  · exact firstMissing?_sound missing
  · exact firstOverlap?_sound overlap
  · exact firstUncovered?_sound uncovered
  · exact firstStale?_sound stale

end Schema

namespace Schema

variable {Snapshot : Type} (schema : Schema Snapshot)

/-- No table of `next` has a new row of an owner that `previous` has (`Table.Frozen`), and every
table declares its owners.  A database after an operation that satisfies this and `Extends`
against the database before it has new owners appended, each with its rows, and gives no owner it
had a new row. -/
@[expose] def Frozen (previous next : Snapshot) : Prop :=
  ∀ entry ∈ schema.tables, entry.table.Frozen previous next

instance (previous next : Snapshot) : Decidable (schema.Frozen previous next) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The first table, in the schema's order, with a new row of an owner that `previous` has, with
the first such row and its owner (`Table.thaw?`). -/
def thaw? (previous next : Snapshot) : Option Thaw :=
  schema.tables.findSome? fun entry ↦ entry.table.thaw? previous next

/-- What a thaw says about `previous` and `next`: some table of the schema holds it
(`Table.Thawed`). -/
@[expose] def Thawed (previous next : Snapshot) (thaw : Thaw) : Prop :=
  ∃ entry ∈ schema.tables, entry.table.Thawed previous next thaw

variable {schema}

theorem thaw?_eq_none {previous next : Snapshot} :
    schema.thaw? previous next = none ↔ schema.Frozen previous next := by
  simp only [thaw?, List.findSome?_eq_none_iff, Table.thaw?_eq_none, Frozen]

/-- What `thaw?` reports is a new row of an owner that `previous` has, as it says. -/
theorem thaw?_sound {previous next : Snapshot} {thaw : Thaw}
    (found : schema.thaw? previous next = some thaw) : schema.Thawed previous next thaw := by
  obtain ⟨entry, member, found⟩ := List.exists_of_findSome?_eq_some found
  exact ⟨entry, member, Table.thaw?_sound found⟩

variable (schema)

/-! ### Checking what a delta adds

For a `next` that is `previous` with the rows of a `delta` added, table by table: whether `next`
is frozen on `previous` (`thawIn?`) and whether a row of `delta` refers forward (`forwardIn?`),
decided by looking at the rows of `delta`, and at `next` or `previous` only where a check needs
to.  Neither looks at a row of `previous` that `delta` does not touch. -/

/-- `thaw?` on `previous` and `next` from the rows `delta` adds, table by table
(`Table.thawIn?`). -/
def thawIn? (previous delta : Snapshot) : Option Thaw :=
  schema.tables.findSome? fun entry ↦ entry.table.thawIn? previous delta

/-- The first table with a row of `delta` that refers to a row written no earlier than its owner
(`Table.forwardIn?`): the table, the column, the owner's place and the place referred to, both
looked up in `rows`. -/
def forwardIn? (rows delta : Snapshot) : Option (String × String × Place × Place) :=
  schema.tables.findSome? fun entry ↦
    (entry.table.forwardIn? rows delta).map fun (column, at_, place) ↦ (entry.table.name, column, at_, place)

variable {schema} in
/-- Where every row of `next` is a row of `previous` or of `delta`, `thawIn?` finding nothing means
that `next` is frozen on `previous`. -/
theorem thawIn?_frozen {previous delta next : Snapshot}
    (split : ∀ entry ∈ schema.tables, ∀ row ∈ entry.table.rows next,
      row ∈ entry.table.rows previous ∨ row ∈ entry.table.rows delta)
    (none : schema.thawIn? previous delta = none) : schema.Frozen previous next :=
  fun entry member ↦
    Table.thawIn?_frozen (split entry member) (List.findSome?_eq_none_iff.mp none entry member)

end Schema

/-- That `schema` passed the schema audit.  `#audit_schema` declares an instance for the schema it
audits, and nothing else can, since the constructor is private.  `Db.load` and `Db.append`
require it, so a schema whose tables read, replace or name the wrong fields of the snapshot holds
no database. -/
class Audited {Snapshot : Type} (schema : Schema Snapshot) : Prop where
  private mk ::

/-- The name of the private constructor of `Audited`, through which `#audit_schema` declares its
instances.  Meta code can reach it, as it can any private name: the audit is closed to terms, not
to metaprograms. -/
def auditedConstructor : Lean.Name := ``Audited.mk

/-- The table `table` is the entry at `position` of the schema's tables, so that an insert into
it names a table of the schema and uses the schema's own functions to add the row.  The schema
audit declares one for every table of an audited schema. -/
class InSchema {Snapshot Row Key : Type} [DecidableEq Row] [TreeOrd Key] {key : Row → Key} (schema : Schema Snapshot)
    (table : Table Snapshot key) where
  position : Fin schema.tables.length
  listed : schema.tables[position] = (table : AnyTable Snapshot)

/-- Where every table's further unique keys hold, those of a table of the schema do: what lets a
reader that has `Schema.Keys` read one table's rows in the order of a further key with no case for
two rows sharing it. -/
theorem Schema.Keys.keyed {Snapshot Row Key : Type} [DecidableEq Row] [TreeOrd Key] {key : Row → Key}
    {schema : Schema Snapshot} {table : Table Snapshot key} [entry : InSchema schema table] {rows : Snapshot}
    (keys : schema.Keys rows) : table.Keyed rows := by
  have member : (table : AnyTable Snapshot) ∈ schema.tables := by
    rw [← entry.listed, Fin.getElem_fin]
    exact List.getElem_mem entry.position.isLt
  exact keys _ member

/-- The further unique keys hold of a snapshot each of whose tables has only rows of the same table of
one they hold of (`Extends`): two rows that share a key in the smaller would share it in the larger. -/
theorem Schema.Keys.of_extends {Snapshot : Type} {schema : Schema Snapshot} {previous next : Snapshot}
    (keys : schema.Keys next) (within : schema.Extends previous next) : schema.Keys previous :=
  fun entry member unique uniqueMember ↦ Relation.keyed_iff_mem.mpr ⟨Rows.toRelation_distinct,
    fun left leftMember right rightMember same ↦
      (keys entry member unique uniqueMember).eq_of_key
        (Rows.mem_toRelation.mpr (within entry member left (Rows.mem_toRelation.mp leftMember)))
        (Rows.mem_toRelation.mpr (within entry member right (Rows.mem_toRelation.mp rightMember))) same⟩

/-- One row to add to a table of `schema`, named by its position in the schema's tables. -/
structure Insert {Snapshot : Type} (schema : Schema Snapshot) where
  position : Fin schema.tables.length
  row : schema.tables[position].Row

/-- The row `row` to add to `table`, a table of the schema. -/
@[expose, inline] def Table.insert {Snapshot Row Key : Type} [DecidableEq Row] [TreeOrd Key]
    {key : Row → Key} {schema : Schema Snapshot} (table : Table Snapshot key)
    [entry : InSchema schema table] (row : Row) : Insert schema :=
  ⟨entry.position, cast (congrArg AnyTable.Row entry.listed).symm row⟩

namespace Insert

variable {Snapshot : Type} {schema : Schema Snapshot}

/-- The row, if the insert is for the table at `position`. -/
def rowAt (insert : Insert schema) (position : Fin schema.tables.length) :
    Option schema.tables[position].Row :=
  if same : insert.position = position then
    some (cast (congrArg (fun position ↦ schema.tables[position].Row) same) insert.row)
  else none

@[simp] theorem rowAt_self (insert : Insert schema) : insert.rowAt insert.position = some insert.row := by
  simp [rowAt]

/-- The table of the insert. -/
def table (insert : Insert schema) : AnyTable Snapshot := schema.tables[insert.position]

/-- The snapshot with the row added to its table and to the table's indexes, through the
table's own functions, unless the table has a row with its primary key.  Nothing checks what the
functions made of it: `append` requires the laws of a schema's readers and writers
(`Schema.Wiring`), from which the rows of the result follow. -/
def apply (insert : Insert schema) (rows : Snapshot) : Snapshot :=
  let current := schema.tables[insert.position].table.rows rows
  if current.contains (schema.tables[insert.position].key insert.row) then rows
  else schema.tables[insert.position].table.indexes.foldl
    (fun rows index ↦ index.set rows ((index.get rows).add insert.row))
    (schema.tables[insert.position].table.set rows (current.insertIfNew insert.row))

/-- A row of the insert's table in `previous`, or of an insert of `delta` for that table, has the
insert's primary key but is a different row. -/
@[expose] def Conflicts (insert : Insert schema) (previous : Snapshot) (delta : List (Insert schema)) : Prop :=
  ∃ row : schema.tables[insert.position].Row, (row ∈ schema.tables[insert.position].table.rows previous ∨
      ∃ other ∈ delta, other.rowAt insert.position = some row) ∧
    schema.tables[insert.position].key row = schema.tables[insert.position].key insert.row ∧
    row ≠ insert.row

/-- An insert whose row is `row` at `position` is for the table at `position`, with that row. -/
theorem rowAt_eq_some {insert : Insert schema} {position : Fin schema.tables.length}
    {row : schema.tables[position].Row} (found : insert.rowAt position = some row) :
    ∃ same : insert.position = position,
      cast (congrArg (fun position ↦ schema.tables[position].Row) same) insert.row = row := by
  unfold rowAt at found
  split at found
  · rename_i same
    cases found
    exact ⟨same, rfl⟩
  · cases found

end Insert

namespace Schema

variable {Snapshot : Type} {schema : Schema Snapshot}

variable (schema) in
/-- The snapshot with every insert of `delta` applied in turn. -/
def applied (previous : Snapshot) (delta : List (Insert schema)) : Snapshot :=
  delta.foldl (fun rows insert ↦ insert.apply rows) previous

/-- `groups` with `insert` added to the inserts at its table's position. -/
private def addToGroup (groups : Array (List (Insert schema))) (insert : Insert schema) :
    Array (List (Insert schema)) :=
  groups.modify insert.position (insert :: ·)

variable (schema) in
/-- The inserts of `delta`, grouped by table: at each table's position, its inserts.  One pass over
the delta, so that what follows looks at each insert once rather than once per table. -/
def grouped (delta : List (Insert schema)) : Array (List (Insert schema)) :=
  delta.foldl addToGroup (Array.replicate schema.tables.length [])

/-- The rows that the inserts of `groups` add to the table at `position`. -/
def rowsAt (groups : Array (List (Insert schema))) (position : Fin schema.tables.length) :
    List schema.tables[position].Row :=
  (groups[position.val]?.getD []).filterMap (·.rowAt position)

private theorem mem_foldl_addToGroup {insert : Insert schema} {position : Fin schema.tables.length} :
    ∀ {delta : List (Insert schema)} {groups : Array (List (Insert schema))},
      groups.size = schema.tables.length →
      (insert ∈ ((delta.foldl addToGroup groups)[position.val]?.getD []) ↔
        insert ∈ (groups[position.val]?.getD []) ∨ (insert ∈ delta ∧ insert.position = position))
  | [], _, _ => by simp
  | first :: rest, groups, size => by
    rw [List.foldl_cons, mem_foldl_addToGroup (by simp [addToGroup, size]), addToGroup,
      Array.getElem?_modify]
    have inside : position.val < groups.size := by rw [size]; exact position.isLt
    rw [Array.getElem?_eq_getElem inside]
    split
    · rename_i same
      have same : first.position = position := Fin.ext same
      simp only [Option.map_some, Option.getD_some, List.mem_cons]
      constructor
      · rintro ((rfl | member) | ⟨later, at_⟩)
        · exact Or.inr ⟨Or.inl rfl, same⟩
        · exact Or.inl member
        · exact Or.inr ⟨Or.inr later, at_⟩
      · rintro (member | ⟨rfl | later, at_⟩)
        · exact Or.inl (Or.inr member)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨later, at_⟩
    · rename_i differs
      simp only [Option.getD_some, List.mem_cons]
      constructor
      · rintro (member | ⟨later, same⟩)
        · exact Or.inl member
        · exact Or.inr ⟨Or.inr later, same⟩
      · rintro (member | ⟨rfl | later, same⟩)
        · exact Or.inl member
        · exact absurd (congrArg Fin.val same) differs
        · exact Or.inr ⟨later, same⟩

theorem mem_rowsAt {delta : List (Insert schema)} {position : Fin schema.tables.length}
    {row : schema.tables[position].Row} :
    row ∈ rowsAt (schema.grouped delta) position ↔ ∃ insert ∈ delta, insert.rowAt position = some row := by
  simp only [rowsAt, List.mem_filterMap]
  constructor
  · rintro ⟨insert, member, found⟩
    rw [grouped, mem_foldl_addToGroup (by simp)] at member
    rcases member with member | ⟨member, _⟩
    · simp at member
    · exact ⟨insert, member, found⟩
  · rintro ⟨insert, member, found⟩
    refine ⟨insert, ?_, found⟩
    rw [grouped, mem_foldl_addToGroup (by simp)]
    exact Or.inr ⟨member, (Insert.rowAt_eq_some found).1⟩

variable (schema) in
/-- Every table of `next` holds exactly the rows of the same table of `previous` and the rows
that `delta` adds to it: no row lost, none from elsewhere. -/
@[expose] def Appended (previous : Snapshot) (delta : List (Insert schema)) (next : Snapshot) : Prop :=
  ∀ position : Fin schema.tables.length, ∀ row : schema.tables[position].Row,
    row ∈ schema.tables[position].table.rows next ↔
      row ∈ schema.tables[position].table.rows previous ∨ ∃ insert ∈ delta, insert.rowAt position = some row

theorem Appended.extends {previous next : Snapshot} {delta : List (Insert schema)}
    (appended : schema.Appended previous delta next) : schema.Extends previous next := by
  intro entry member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  subst same
  exact fun row inPrevious ↦ (appended ⟨index, bound⟩ row).mpr (Or.inl inPrevious)

theorem Appended.added {previous next : Snapshot} {delta : List (Insert schema)}
    (appended : schema.Appended previous delta next) :
    ∀ insert ∈ delta, insert.row ∈ schema.tables[insert.position].table.rows next :=
  fun insert member ↦ (appended insert.position insert.row).mpr
    (Or.inr ⟨insert, member, insert.rowAt_self⟩)

end Schema

/-- Why an append is refused: a conflict between rows, or a constraint the result violates. -/
inductive Refusal where
  /-- An appended row of `table` has the primary key `key` of a different row, of the table or of
  the delta. -/
  | conflict (table key : String)
  /-- The result violates a constraint of the schema. -/
  | invalid (violation : Violation)
  deriving @[expose] DecidableEq, Repr

namespace Schema

variable {Snapshot : Type} (schema : Schema Snapshot)

/-- What a refusal says about appending `delta` to `previous`. -/
@[expose] def Refuses (previous : Snapshot) (delta : List (Insert schema)) : Refusal → Prop
  | .conflict table key => ∃ insert ∈ delta, schema.tables[insert.position].table.name = table ∧
      schema.tables[insert.position].table.primaryName = key ∧ insert.Conflicts previous delta
  | .invalid violation => schema.Violated (schema.applied previous delta) violation

-- with its `by` proofs private, the match below fails ("the type of pattern variable contains
-- metavariables")
set_option backward.proofsInPublic true in
/-- The table and primary key of the first table, in the schema's order, with an insert of `delta`
whose row has the primary key of a different row, of the table or of the delta: the delta's rows
for each table inserted into a copy of the table's tree, in O(d log (n + d)) time for d rows of the
delta and n of the table, besides a search over the positions of the T tables, each looked up in
the list of tables: O(T²). -/
def firstConflict? (previous : Snapshot) (delta : List (Insert schema)) : Option Refusal :=
  let groups := schema.grouped delta
  (List.finRange schema.tables.length).findSome? fun position ↦
    match (schema.tables[position].table.rows previous).insertAll? (rowsAt groups position) with
    | .error _ =>
      some (.conflict schema.tables[position].table.name schema.tables[position].table.primaryName)
    | .ok _ => none

variable {schema}

theorem firstConflict?_sound {previous : Snapshot} {delta : List (Insert schema)}
    {refusal : Refusal} (found : schema.firstConflict? previous delta = some refusal) :
    schema.Refuses previous delta refusal := by
  obtain ⟨position, _, found⟩ := List.exists_of_findSome?_eq_some found
  split at found
  · rename_i row refused
    cases found
    obtain ⟨added, other, member, same, differs⟩ := Rows.insertAll?_eq_error refused
    obtain ⟨insert, inDelta, rowFound⟩ := mem_rowsAt.mp added
    obtain ⟨rfl, rfl⟩ := Insert.rowAt_eq_some rowFound
    refine ⟨insert, inDelta, rfl, rfl, other, ?_, same, differs⟩
    rcases member with member | member
    · exact Or.inl member
    · exact Or.inr (mem_rowsAt.mp member)
  · cases found

end Schema

/-- Whether two snapshots hold the same rows in every table of the schema: the tables are sets of
rows, compared row by row, never by an order of their keys. -/
def Schema.sameRows {Snapshot : Type} (schema : Schema Snapshot) (left right : Snapshot) : Bool :=
  schema.tables.all fun entry ↦
    (entry.table.rows left).included (entry.table.rows right) &&
      (entry.table.rows right).included (entry.table.rows left)

theorem Schema.sameRows_iff {Snapshot : Type} {schema : Schema Snapshot} {left right : Snapshot} :
    schema.sameRows left right = true ↔
      ∀ entry ∈ schema.tables, entry.table.rows left = entry.table.rows right := by
  simp only [Schema.sameRows, List.all_eq_true, Bool.and_eq_true, Rows.included_iff]
  refine forall_congr' fun entry ↦ imp_congr_right fun _ ↦ ⟨fun ⟨there, back⟩ ↦
    Rows.ext fun row ↦ ⟨there row, back row⟩, fun same ↦ ?_⟩
  rw [same]
  exact ⟨fun _ member ↦ member, fun _ member ↦ member⟩

end Relational
