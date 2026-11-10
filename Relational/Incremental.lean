module

public import Relational.Lens
import all Relational.Database

public section

namespace Relational

/-! Appending a delta by its rows alone, for a schema whose readers and writers satisfy their laws
(`Schema.Wiring`): what `Insert.apply` makes of a snapshot follows from the laws, so that the
rows of the result need no check against the rows of the old database and the delta. -/

namespace Schema

variable {Snapshot : Type} {schema : Schema Snapshot}

/-- No two different rows of a table, among its rows in `rows` and those that `delta` adds to it,
share a primary key. -/
@[expose] def KeysAgree (rows : Snapshot) (delta : List (Insert schema)) : Prop :=
  ∀ (q : Fin schema.tables.length) (a b : schema.tables[q].Row),
    (a ∈ schema.tables[q].table.rows rows ∨ ∃ insert ∈ delta, insert.rowAt q = some a) →
    (b ∈ schema.tables[q].table.rows rows ∨ ∃ insert ∈ delta, insert.rowAt q = some b) →
    schema.tables[q].key a = schema.tables[q].key b → a = b

/-- Writing an index of a table leaves every table's rows alone. -/
theorem Wiring.rows_index_set_mem [wiring : schema.Wiring] {p : Fin schema.tables.length}
    {index : TableIndex Snapshot schema.tables[p].key}
    (member : index ∈ schema.tables[p].table.indexes) (q : Fin schema.tables.length) (s : Snapshot)
    (v : Index schema.tables[p].key index.column) :
    schema.tables[q].table.rows (index.set s v) = schema.tables[q].table.rows s := by
  obtain ⟨j, bound, rfl⟩ := List.getElem_of_mem member
  exact wiring.rows_index_set p ⟨j, bound⟩ q s v

/-- Adding a row to some indexes of a table leaves every table's rows alone. -/
theorem Wiring.rows_foldl_indexes [schema.Wiring] {p : Fin schema.tables.length}
    (row : schema.tables[p].Row) (q : Fin schema.tables.length) :
    ∀ (indexes : List (TableIndex Snapshot schema.tables[p].key)),
      (∀ index ∈ indexes, index ∈ schema.tables[p].table.indexes) → ∀ s : Snapshot,
      schema.tables[q].table.rows
          (indexes.foldl (fun rows index ↦ index.set rows ((index.get rows).add row)) s) =
        schema.tables[q].table.rows s
  | [], _, _ => rfl
  | index :: rest, within, s => by
    rw [List.foldl_cons,
      rows_foldl_indexes row q rest (fun other member ↦ within other (List.mem_cons_of_mem _ member)),
      rows_index_set_mem (within index List.mem_cons_self)]

/-- The rows of a table after an insert: those before, and the insert's row if it is for the
table and the table has no row with its primary key. -/
theorem _root_.Relational.Insert.mem_rows_apply [schema.Wiring] (insert : Insert schema) (s : Snapshot)
    (q : Fin schema.tables.length) (row : schema.tables[q].Row) :
    row ∈ schema.tables[q].table.rows (insert.apply s) ↔ row ∈ schema.tables[q].table.rows s ∨
      (insert.rowAt q = some row ∧
        (schema.tables[q].table.rows s).contains (schema.tables[q].key row) = false) := by
  by_cases same : insert.position = q
  · subst same
    simp only [Insert.rowAt_self, Option.some.injEq]
    dsimp only [Insert.apply]
    split
    · rename_i present
      constructor
      · exact Or.inl
      · rintro (member | ⟨rfl, absent⟩)
        · exact member
        · simp only [Fin.getElem_fin] at present absent
          simp [present] at absent
    · rw [Wiring.rows_foldl_indexes _ _ _ (fun _ member ↦ member), Wiring.rows_set,
        Rows.mem_insertIfNew]
      constructor
      · rintro (member | ⟨rfl, absent⟩)
        · exact Or.inl member
        · exact Or.inr ⟨rfl, absent⟩
      · rintro (member | ⟨rfl, absent⟩)
        · exact Or.inl member
        · exact Or.inr ⟨rfl, absent⟩
  · have none : insert.rowAt q = none := by simp [Insert.rowAt, same]
    simp only [none, reduceCtorEq, false_and, or_false]
    dsimp only [Insert.apply]
    split
    · exact Iff.rfl
    · rw [Wiring.rows_foldl_indexes _ _ _ (fun _ member ↦ member), Wiring.rows_set_ne _ _ same]

/-- A row of a table of `rows`, or one that `delta` adds, after an insert: one of `rows`, or one
that the insert or `delta` adds. -/
private theorem lift_apply [schema.Wiring] {insert : Insert schema} {rest : List (Insert schema)}
    {s : Snapshot} {q : Fin schema.tables.length} {a : schema.tables[q].Row}
    (member : a ∈ schema.tables[q].table.rows (insert.apply s) ∨
      ∃ other ∈ rest, other.rowAt q = some a) :
    a ∈ schema.tables[q].table.rows s ∨ ∃ other ∈ insert :: rest, other.rowAt q = some a := by
  rcases member with member | ⟨other, inRest, found⟩
  · rcases (insert.mem_rows_apply s q a).mp member with member | ⟨found, _⟩
    · exact Or.inl member
    · exact Or.inr ⟨insert, List.mem_cons_self, found⟩
  · exact Or.inr ⟨other, List.mem_cons_of_mem _ inRest, found⟩

/-- Where no two different rows of a table, old or added, share a primary key, every table of
the applied delta holds exactly its old rows and the delta's. -/
theorem mem_applied [schema.Wiring] :
    ∀ {delta : List (Insert schema)} {s : Snapshot}, schema.KeysAgree s delta →
      ∀ (q : Fin schema.tables.length) (row : schema.tables[q].Row),
        row ∈ schema.tables[q].table.rows (schema.applied s delta) ↔
          row ∈ schema.tables[q].table.rows s ∨ ∃ insert ∈ delta, insert.rowAt q = some row
  | [], _, _, _, _ => by simp [applied]
  | insert :: rest, s, agree, q, row => by
    have step : schema.applied s (insert :: rest) = schema.applied (insert.apply s) rest := rfl
    have agree' : schema.KeysAgree (insert.apply s) rest :=
      fun q a b inA inB same ↦ agree q a b (lift_apply inA) (lift_apply inB) same
    rw [step, mem_applied agree' q row, insert.mem_rows_apply s q row]
    constructor
    · rintro ((member | ⟨found, _⟩) | ⟨other, inRest, found⟩)
      · exact Or.inl member
      · exact Or.inr ⟨insert, List.mem_cons_self, found⟩
      · exact Or.inr ⟨other, List.mem_cons_of_mem _ inRest, found⟩
    · rintro (member | ⟨other, inDelta, found⟩)
      · exact Or.inl (Or.inl member)
      · rcases List.mem_cons.mp inDelta with rfl | inRest
        · cases present : (schema.tables[q].table.rows s).contains (schema.tables[q].key row)
          · exact Or.inl (Or.inr ⟨found, rfl⟩)
          · obtain ⟨old, inOld, same⟩ := Rows.contains_iff.mp present
            have equal := agree q old row (Or.inl inOld) (Or.inr ⟨other, List.mem_cons_self, found⟩) same
            exact Or.inl (Or.inl (equal ▸ inOld))
        · exact Or.inr ⟨other, inRest, found⟩

/-- Where no two different rows of a table share a primary key, the applied delta is appended. -/
theorem appended_of_keysAgree [schema.Wiring] {previous : Snapshot} {delta : List (Insert schema)}
    (agree : schema.KeysAgree previous delta) :
    schema.Appended previous delta (schema.applied previous delta) :=
  fun q row ↦ mem_applied agree q row

/-- `firstConflict?` finding nothing means that no two different rows of a table share a primary
key. -/
theorem keysAgree_of_firstConflict?_eq_none {previous : Snapshot} {delta : List (Insert schema)}
    (none : schema.firstConflict? previous delta = none) : schema.KeysAgree previous delta := by
  intro q a b inA inB same
  have atQ := List.findSome?_eq_none_iff.mp none q (List.mem_finRange q)
  cases merged : (schema.tables[q].table.rows previous).insertAll? (rowsAt (schema.grouped delta) q) with
  | error _ => simp only [merged, reduceCtorEq] at atQ
  | ok rows =>
    have inside (c : schema.tables[q].Row)
        (member : c ∈ schema.tables[q].table.rows previous ∨ ∃ insert ∈ delta, insert.rowAt q = some c) :
        c ∈ rows :=
      (Rows.mem_insertAll? merged c).mpr (member.imp id mem_rowsAt.mpr)
    exact Rows.key_injective (inside a inA) (inside b inB) same

/-! ### Coherence: which table a constraint reads

The constraints of a schema read the snapshot through functions (`ForeignKey.parents`,
`Participation.parents`, `Subtyping.supertype`, `SubtypeMember.keys`) whose types do not say which
table of the schema they read.  The incremental check needs it: a parent that the grown database has
and the old one lacked is the image of a row that the delta adds to that table.  `ReadsTable` states
it for one such function, and `Coherent` for every one of a schema.  The schema audit checks the
corresponding facts up to definitional equality for owners and root foreign keys only; a generator
for `Coherent` must find the table by name and check the conversion. -/

/-- `read` reads the rows of the table at `position`, each through `conv`. -/
structure ReadsTable (schema : Schema Snapshot) {X : Type} (read : Snapshot → Relation X) where
  position : Fin schema.tables.length
  conv : schema.tables[position].Row → X
  mem_iff : ∀ (s : Snapshot) (x : X),
    x ∈ read s ↔ ∃ row : schema.tables[position].Row,
      row ∈ schema.tables[position].table.rows s ∧ conv row = x

/-- A function that is the relation of a table's rows reads that table, each row as itself. -/
def ReadsTable.ofRows (position : Fin schema.tables.length)
    (read : Snapshot → Relation schema.tables[position].Row)
    (same : ∀ s, read s = (schema.tables[position].table.rows s).toRelation) :
    schema.ReadsTable read :=
  ⟨position, id, fun s x ↦ by rw [same]; simp⟩

/-- Every function through which a constraint of `schema` reads the snapshot reads one table of
the schema: each foreign key's and mandatory participation's parents, each subtyping's supertype
and each member's keys. -/
class Coherent (schema : Schema Snapshot) where
  foreignKey : ∀ (p : Fin schema.tables.length) (j : Fin schema.tables[p].table.foreignKeys.length),
    schema.ReadsTable schema.tables[p].table.foreignKeys[j].parents
  participation : ∀ (p : Fin schema.tables.length)
    (j : Fin schema.tables[p].table.participations.length),
    schema.ReadsTable schema.tables[p].table.participations[j].parents
  supertype : ∀ k : Fin schema.subtypings.length,
    schema.ReadsTable fun s ↦ (schema.subtypings[k].supertype.table.rows s).toRelation
  member : ∀ (k : Fin schema.subtypings.length) (m : Fin schema.subtypings[k].members.length),
    schema.ReadsTable schema.subtypings[k].members[m].keys

/-- What a table-reading function reads only grows as the tables grow. -/
theorem ReadsTable.mono {X : Type} {read : Snapshot → Relation X} (reads : schema.ReadsTable read)
    {previous next : Snapshot} (grown : schema.Extends previous next) {x : X}
    (member : x ∈ read previous) : x ∈ read next := by
  obtain ⟨row, inPrevious, rfl⟩ := (reads.mem_iff previous x).mp member
  refine (reads.mem_iff next _).mpr ⟨row, ?_, rfl⟩
  exact grown _ (List.getElem_mem reads.position.isLt) row inPrevious

/-- After a delta is appended, a table-reading function reads what it read before and the images
of the rows the delta adds to its table: the new parents, supertype rows or member keys are found
from the delta alone. -/
theorem ReadsTable.mem_appended {X : Type} {read : Snapshot → Relation X}
    (reads : schema.ReadsTable read) {previous next : Snapshot} {delta : List (Insert schema)}
    (appended : schema.Appended previous delta next) (x : X) :
    x ∈ read next ↔ x ∈ read previous ∨
      ∃ insert ∈ delta, ∃ row, insert.rowAt reads.position = some row ∧ reads.conv row = x := by
  rw [reads.mem_iff next x, reads.mem_iff previous x]
  constructor
  · rintro ⟨row, member, rfl⟩
    rcases (appended reads.position row).mp member with old | ⟨insert, inDelta, found⟩
    · exact Or.inl ⟨row, old, rfl⟩
    · exact Or.inr ⟨insert, inDelta, row, found, rfl⟩
  · rintro (⟨row, old, rfl⟩ | ⟨insert, inDelta, row, found, rfl⟩)
    · exact ⟨row, (appended reads.position row).mpr (Or.inl old), rfl⟩
    · exact ⟨row, (appended reads.position row).mpr (Or.inr ⟨insert, inDelta, found⟩), rfl⟩

end Schema

end Relational
