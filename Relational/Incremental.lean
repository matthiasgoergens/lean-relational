module

public import Relational.Lens
public import Relational.HTuple
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

/-! ### User indexes after an insert -/

/-- Adding a row to the indexes of a table from position `k` of its list on: the index at
position `j` gets the row if `k ≤ j`, and is left alone otherwise. -/
theorem Wiring.index_get_foldl [wiring : schema.Wiring] {p : Fin schema.tables.length}
    (row : schema.tables[p].Row) (j : Fin schema.tables[p].table.indexes.length) :
    ∀ (k : Nat) (s : Snapshot),
      (schema.indexAt p j).get
          ((schema.tables[p].table.indexes.drop k).foldl
            (fun rows index ↦ index.set rows ((index.get rows).add row)) s) =
        if k ≤ j.val then ((schema.indexAt p j).get s).add row else (schema.indexAt p j).get s
  | k, s => by
    by_cases inside : k < schema.tables[p].table.indexes.length
    · rw [List.drop_eq_getElem_cons inside, List.foldl_cons, index_get_foldl row j (k + 1)]
      by_cases same : k = j.val
      · have : j = ⟨k, inside⟩ := Fin.ext same.symm
        subst this
        have law := wiring.index_get_set p ⟨k, inside⟩ s
          ((schema.indexAt p ⟨k, inside⟩).get s |>.add row)
        simp only [Nat.le_refl, ite_true, Nat.not_succ_le_self, ite_false]
        exact law
      · have law := wiring.index_get_set_ne p ⟨k, inside⟩ p j (Or.inr same) s
          ((schema.indexAt p ⟨k, inside⟩).get s |>.add row)
        have step : (k + 1 ≤ j.val) = (k ≤ j.val) := by
          apply propext; omega
        simp only [step]
        exact law ▸ rfl
    · have empty : schema.tables[p].table.indexes.drop k = [] :=
        List.drop_eq_nil_of_le (Nat.le_of_not_lt inside)
      have later : ¬ k ≤ j.val := by have := j.isLt; omega
      rw [empty]
      simp [later]
termination_by k => schema.tables[p].table.indexes.length - k
decreasing_by simp only [Fin.getElem_fin] at *; omega

/-- Adding a row to all indexes of a table leaves the indexes of other tables alone. -/
theorem Wiring.index_get_foldl_ne [wiring : schema.Wiring] {p q : Fin schema.tables.length}
    (row : schema.tables[p].Row) (differs : p ≠ q) (l : Fin schema.tables[q].table.indexes.length) :
    ∀ (k : Nat) (s : Snapshot),
      (schema.indexAt q l).get
          ((schema.tables[p].table.indexes.drop k).foldl
            (fun rows index ↦ index.set rows ((index.get rows).add row)) s) =
        (schema.indexAt q l).get s
  | k, s => by
    by_cases inside : k < schema.tables[p].table.indexes.length
    · rw [List.drop_eq_getElem_cons inside, List.foldl_cons, index_get_foldl_ne row differs l (k + 1)]
      exact wiring.index_get_set_ne p ⟨k, inside⟩ q l (Or.inl differs) s _
    · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt inside)]
      rfl
termination_by k => schema.tables[p].table.indexes.length - k
decreasing_by simp only [Fin.getElem_fin] at *; omega

/-- Every index of every table agrees with its table after an insert, if it did before. -/
theorem _root_.Relational.Insert.indexed_apply [wiring : schema.Wiring] (insert : Insert schema) {s : Snapshot}
    (indexed : ∀ (q : Fin schema.tables.length) (l : Fin schema.tables[q].table.indexes.length),
      ((schema.indexAt q l).get s).Agrees (schema.tables[q].table.rows s))
    (q : Fin schema.tables.length) (l : Fin schema.tables[q].table.indexes.length) :
    ((schema.indexAt q l).get (insert.apply s)).Agrees (schema.tables[q].table.rows (insert.apply s)) := by
  dsimp only [Insert.apply]
  split
  · exact indexed q l
  · rename_i fresh
    rw [Wiring.rows_foldl_indexes _ _ _ (fun _ member ↦ member)]
    by_cases same : insert.position = q
    · subst same
      have all := Wiring.index_get_foldl (schema := schema) insert.row l 0
        (schema.tables[insert.position].table.set s
          ((schema.tables[insert.position].table.rows s).insertIfNew insert.row))
      simp only [List.drop_zero, Nat.zero_le, ite_true] at all
      rw [all, wiring.index_get_rows_set, wiring.rows_set]
      exact Index.agrees_add (indexed _ l) (Bool.eq_false_iff.mpr fresh)
    · have other := Wiring.index_get_foldl_ne (schema := schema) insert.row same l 0
        (schema.tables[insert.position].table.set s
          ((schema.tables[insert.position].table.rows s).insertIfNew insert.row))
      simp only [List.drop_zero] at other
      rw [other, wiring.index_get_rows_set, wiring.rows_set_ne _ _ same]
      exact indexed q l

/-- Every index of every table agrees with its table after a delta is applied, if it did before. -/
theorem indexed_applied [schema.Wiring] :
    ∀ {delta : List (Insert schema)} {s : Snapshot},
      (∀ (q : Fin schema.tables.length) (l : Fin schema.tables[q].table.indexes.length),
        ((schema.indexAt q l).get s).Agrees (schema.tables[q].table.rows s)) →
      ∀ (q : Fin schema.tables.length) (l : Fin schema.tables[q].table.indexes.length),
        ((schema.indexAt q l).get (schema.applied s delta)).Agrees
          (schema.tables[q].table.rows (schema.applied s delta))
  | [], _, indexed => indexed
  | insert :: rest, _, indexed => indexed_applied (delta := rest) (insert.indexed_apply indexed)

/-- `Indexed`, over positions. -/
theorem indexed_iff {s : Snapshot} :
    schema.Indexed s ↔ ∀ (q : Fin schema.tables.length) (l : Fin schema.tables[q].table.indexes.length),
      ((schema.indexAt q l).get s).Agrees (schema.tables[q].table.rows s) := by
  constructor
  · intro indexed q l
    exact indexed _ (List.getElem_mem q.isLt) _ (List.getElem_mem l.isLt)
  · intro indexed entry member index inside
    obtain ⟨q, bound, rfl⟩ := List.getElem_of_mem member
    obtain ⟨l, bound', rfl⟩ := List.getElem_of_mem inside
    exact indexed ⟨q, bound⟩ ⟨l, bound'⟩

/-- `Indexed` holds after a delta is applied, if it held before. -/
theorem Indexed.applied [schema.Wiring] {s : Snapshot} (indexed : schema.Indexed s)
    (delta : List (Insert schema)) : schema.Indexed (schema.applied s delta) :=
  indexed_iff.mpr (indexed_applied (indexed_iff.mp indexed))

/-! ### Primary keys: `firstConflict?` decides `KeysAgree` -/

theorem firstConflict?_eq_none_of_keysAgree {previous : Snapshot} {delta : List (Insert schema)}
    (agree : schema.KeysAgree previous delta) : schema.firstConflict? previous delta = none := by
  refine List.findSome?_eq_none_iff.mpr fun q _ ↦ ?_
  obtain ⟨rows, merged⟩ := Rows.insertAll?_ok (rows := schema.tables[q].table.rows previous)
    (added := rowsAt (schema.grouped delta) q) fun a b inA inB same ↦
      agree q a b (inA.imp id mem_rowsAt.mp) (inB.imp id mem_rowsAt.mp) same
  simp only [merged]

theorem firstConflict?_eq_none_iff {previous : Snapshot} {delta : List (Insert schema)} :
    schema.firstConflict? previous delta = none ↔ schema.KeysAgree previous delta :=
  ⟨keysAgree_of_firstConflict?_eq_none, firstConflict?_eq_none_of_keysAgree⟩

/-! ### The indexes a database keeps

Per table, one index per further unique key (the rows by the key's value) and one per mandatory
participation (the rows by the column that refers to the parent), so that a new row's unique keys
and a new parent's participations are each probed in O(log n). -/

/-- The indexes kept for one table: by each further unique key, and by each mandatory
participation's referring column. -/
@[expose, reducible] def TableIndexes (entry : AnyTable Snapshot) : Type :=
  HTuple (fun unique : UniqueKey entry.Row ↦ Index entry.key unique.key) entry.table.uniqueKeys ×
    HTuple (fun participation : Participation Snapshot entry.Row ↦ Index entry.key participation.reference)
      entry.table.participations

namespace TableIndexes

/-- The indexes of a table's rows. -/
def ofRows (entry : AnyTable Snapshot) (rows : Rows entry.key) : TableIndexes entry :=
  (HTuple.build (fun _ ↦ Index.ofRows rows) _, HTuple.build (fun _ ↦ Index.ofRows rows) _)

/-- The indexes with a row added. -/
def add (entry : AnyTable Snapshot) (row : entry.Row) (indexes : TableIndexes entry) : TableIndexes entry :=
  (indexes.1.map (fun _ index ↦ index.add row), indexes.2.map (fun _ index ↦ index.add row))

/-- Each index agrees with the table's rows. -/
@[expose] def Agrees {entry : AnyTable Snapshot} (indexes : TableIndexes entry) (rows : Rows entry.key) : Prop :=
  (∀ j : Fin entry.table.uniqueKeys.length, (indexes.1.get j).Agrees rows) ∧
    ∀ j : Fin entry.table.participations.length, (indexes.2.get j).Agrees rows

theorem agrees_ofRows {entry : AnyTable Snapshot} (rows : Rows entry.key) : (ofRows entry rows).Agrees rows :=
  ⟨fun j ↦ by rw [ofRows, HTuple.get_build]; exact Index.agrees_ofRows,
    fun j ↦ by rw [ofRows, HTuple.get_build]; exact Index.agrees_ofRows⟩

theorem agrees_add {entry : AnyTable Snapshot} {indexes : TableIndexes entry} {rows : Rows entry.key}
    {row : entry.Row} (agrees : indexes.Agrees rows) (fresh : rows.contains (entry.key row) = false) :
    (add entry row indexes).Agrees (rows.insertIfNew row) :=
  ⟨fun j ↦ by rw [add, HTuple.get_map]; exact Index.agrees_add (agrees.1 j) fresh,
    fun j ↦ by rw [add, HTuple.get_map]; exact Index.agrees_add (agrees.2 j) fresh⟩

end TableIndexes

variable (schema) in
/-- The indexes kept for every table of the schema, in the order of its tables. -/
@[expose, reducible] def Indexes : Type := HTuple TableIndexes schema.tables

variable (schema) in
/-- The indexes of every table of a snapshot, in O(n log n) time for n rows. -/
def Indexes.ofSnapshot (s : Snapshot) : schema.Indexes :=
  HTuple.build (fun entry ↦ TableIndexes.ofRows entry (entry.table.rows s)) schema.tables

/-- Every index kept for every table agrees with the table's rows in `s`. -/
@[expose] def IndexesAgree (s : Snapshot) (indexes : schema.Indexes) : Prop :=
  ∀ p : Fin schema.tables.length, (HTuple.get indexes p).Agrees (schema.tables[p].table.rows s)

theorem indexesAgree_ofSnapshot (s : Snapshot) : schema.IndexesAgree s (Indexes.ofSnapshot schema s) := by
  intro p
  unfold Indexes.ofSnapshot
  rw [HTuple.get_build]
  exact TableIndexes.agrees_ofRows _

/-- The indexes with the insert's row added to those of its table, unless the table has a row with
its primary key in `s`: as `Insert.apply` adds it to the table. -/
def _root_.Relational.Insert.addIndexes (insert : Insert schema) (s : Snapshot) (indexes : schema.Indexes) :
    schema.Indexes :=
  if (schema.tables[insert.position].table.rows s).contains (schema.tables[insert.position].key insert.row)
  then indexes
  else HTuple.modify indexes insert.position (TableIndexes.add _ insert.row)

variable (schema) in
/-- The snapshot and its indexes with every insert of `delta` applied in turn. -/
def grow (previous : Snapshot) (indexes : schema.Indexes) (delta : List (Insert schema)) :
    Snapshot × schema.Indexes :=
  delta.foldl (fun (s, indexes) insert ↦ (insert.apply s, insert.addIndexes s indexes)) (previous, indexes)

theorem grow_fst : ∀ (delta : List (Insert schema)) (previous : Snapshot) (indexes : schema.Indexes),
    (schema.grow previous indexes delta).1 = schema.applied previous delta
  | [], _, _ => rfl
  | insert :: rest, previous, indexes => grow_fst rest (insert.apply previous) (insert.addIndexes previous indexes)

/-- The insert's table after the insert, where it lacked the row's primary key. -/
theorem _root_.Relational.Insert.rows_apply_self [schema.Wiring] (insert : Insert schema) (s : Snapshot)
    (fresh : (schema.tables[insert.position].table.rows s).contains
      (schema.tables[insert.position].key insert.row) = false) :
    schema.tables[insert.position].table.rows (insert.apply s) =
      (schema.tables[insert.position].table.rows s).insertIfNew insert.row := by
  dsimp only [Insert.apply]
  split
  · rename_i present
    simp only [Fin.getElem_fin] at present fresh
    simp [present] at fresh
  · rw [Wiring.rows_foldl_indexes _ _ _ (fun _ member ↦ member), Wiring.rows_set]

/-- Another table after an insert. -/
theorem _root_.Relational.Insert.rows_apply_ne [schema.Wiring] (insert : Insert schema) (s : Snapshot)
    {q : Fin schema.tables.length} (differs : insert.position ≠ q) :
    schema.tables[q].table.rows (insert.apply s) = schema.tables[q].table.rows s := by
  dsimp only [Insert.apply]
  split
  · rfl
  · rw [Wiring.rows_foldl_indexes _ _ _ (fun _ member ↦ member), Wiring.rows_set_ne _ _ differs]

theorem _root_.Relational.Insert.indexesAgree_apply [schema.Wiring] (insert : Insert schema) {s : Snapshot}
    {indexes : schema.Indexes} (agree : schema.IndexesAgree s indexes) :
    schema.IndexesAgree (insert.apply s) (insert.addIndexes s indexes) := by
  intro q
  unfold Insert.addIndexes
  cases fresh : (schema.tables[insert.position].table.rows s).contains
      (schema.tables[insert.position].key insert.row)
  case true =>
    have same : insert.apply s = s := by
      dsimp only [Insert.apply]
      simp only [Fin.getElem_fin] at fresh ⊢
      simp only [fresh, ↓reduceIte]
    simp only [↓reduceIte, same]
    exact agree q
  case false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases same : insert.position = q
    · subst same
      rw [HTuple.get_modify_self, insert.rows_apply_self s fresh]
      exact TableIndexes.agrees_add (agree _) fresh
    · rw [HTuple.get_modify_ne _ _ _ _ same, insert.rows_apply_ne s same]
      exact agree q

theorem indexesAgree_grow [schema.Wiring] :
    ∀ (delta : List (Insert schema)) {previous : Snapshot} {indexes : schema.Indexes},
      schema.IndexesAgree previous indexes →
      schema.IndexesAgree (schema.grow previous indexes delta).1 (schema.grow previous indexes delta).2
  | [], _, _, agree => agree
  | insert :: rest, _, _, agree => indexesAgree_grow rest (insert.indexesAgree_apply agree)

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

/-! ### What the incremental check accepts

`Accepts previous delta` states, for the delta applied as a set, the probes that decide whether
the grown database is valid, given that `previous` is: each looks at a row the delta adds and
probes the grown database at one key.  The probes are stated on `applied previous delta`, which
`Insert.apply` builds in O(d log n); deciding them in O(d log n) needs the database's indexes
(one per further unique key, one per mandatory participation), which the next stage adds. -/

variable (schema) in
/-- The delta's rows, applied as a set to `previous`, keep every primary key, further unique key,
foreign key, mandatory participation and subtyping, as far as a row they add can break it. -/
@[expose] def Accepts [coherent : schema.Coherent] (previous : Snapshot) (delta : List (Insert schema)) :
    Prop :=
  let next := schema.applied previous delta
  -- primary keys: no two different rows of a table, old or new, share one
  schema.KeysAgree previous delta ∧
  -- further unique keys: no other row of the grown table shares a new row's value
  (∀ insert ∈ delta, ∀ unique : UniqueKey schema.tables[insert.position].Row,
    unique ∈ schema.tables[insert.position].table.uniqueKeys →
    ∀ other : schema.tables[insert.position].Row, other ∈ schema.tables[insert.position].table.rows next →
      unique.key other = unique.key insert.row → other = insert.row) ∧
  -- foreign keys: a new row finds an allowed parent in the grown database
  (∀ insert ∈ delta, ∀ foreign : ForeignKey Snapshot schema.tables[insert.position].Row,
    foreign ∈ schema.tables[insert.position].table.foreignKeys →
    ∃ parent ∈ foreign.parents next, foreign.allowed insert.row parent = true ∧
      foreign.primary parent = foreign.reference insert.row) ∧
  -- mandatory participations: a new parent row in scope has a child in the grown database
  (∀ (p : Fin schema.tables.length) (j : Fin schema.tables[p].table.participations.length),
    ∀ insert ∈ delta, ∀ row, insert.rowAt (coherent.participation p j).position = some row →
      schema.tables[p].table.participations[j].scope ((coherent.participation p j).conv row) = true →
      ∃ child : schema.tables[p].Row, child ∈ schema.tables[p].table.rows next ∧
        schema.tables[p].table.participations[j].reference child =
          schema.tables[p].table.participations[j].primary ((coherent.participation p j).conv row)) ∧
  -- subtype members: a new member row has a supertype row of one of its facts, and its key is in no
  -- other member
  (∀ (k : Fin schema.subtypings.length) (m : Fin schema.subtypings[k].members.length),
    ∀ insert ∈ delta, ∀ row, insert.rowAt (coherent.member k m).position = some row →
      (∃ parent : schema.subtypings[k].supertype.Row,
        parent ∈ schema.subtypings[k].supertype.table.rows next ∧
        schema.subtypings[k].supertype.key parent = (coherent.member k m).conv row ∧
          schema.subtypings[k].members[m].facts.Contains (schema.subtypings[k].fact parent)) ∧
      ∀ other : Fin schema.subtypings[k].members.length, other ≠ m →
        (coherent.member k m).conv row ∉ schema.subtypings[k].members[other].keys next) ∧
  -- covering and exhaustive subtypings: a new supertype row in scope is in some member
  (∀ k : Fin schema.subtypings.length, ∀ insert ∈ delta, ∀ row,
    insert.rowAt (coherent.supertype k).position = some row →
      schema.subtypings[k].inScope ((coherent.supertype k).conv row) = true →
      ∃ member : SubtypeMember Snapshot schema.subtypings[k].supertype.Key schema.subtypings[k].Fact,
        member ∈ schema.subtypings[k].members ∧
        schema.subtypings[k].supertype.key ((coherent.supertype k).conv row) ∈ member.keys next)

end Schema

end Relational
