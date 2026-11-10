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
@[expose] def ReadsTable.ofRows (position : Fin schema.tables.length)
    (read : Snapshot → Relation schema.tables[position].Row)
    (same : ∀ s, read s = (schema.tables[position].table.rows s).toRelation) :
    schema.ReadsTable read :=
  ⟨position, id, fun s x ↦ by rw [same]; simp⟩

/-- A function that is the relation of a table's rows, each projected by `key`, reads that table,
each row as its projection: the keys of a subtype table. -/
@[expose] def ReadsTable.ofProject {X : Type} (position : Fin schema.tables.length)
    (key : schema.tables[position].Row → X) (read : Snapshot → Relation X)
    (same : ∀ s, read s = (schema.tables[position].table.rows s).toRelation.project key) :
    schema.ReadsTable read :=
  ⟨position, key, fun s x ↦ by rw [same]; simp⟩

variable (schema) in
/-- For one table, the table that each of its foreign keys and mandatory participations reads. -/
@[expose, reducible] def TableReads (entry : AnyTable Snapshot) : Type :=
  HTuple (fun foreign : ForeignKey Snapshot entry.Row ↦ schema.ReadsTable foreign.parents)
      entry.table.foreignKeys ×
    HTuple (fun participation : Participation Snapshot entry.Row ↦ schema.ReadsTable participation.parents)
      entry.table.participations

variable (schema) in
/-- For one subtyping, the table its supertype reads, and the table each member's keys read. -/
@[expose, reducible] def SubtypingReads (subtyping : Subtyping Snapshot) : Type :=
  schema.ReadsTable (fun s ↦ (subtyping.supertype.table.rows s).toRelation) ×
    HTuple (fun member : SubtypeMember Snapshot subtyping.supertype.Key subtyping.Fact ↦
      schema.ReadsTable member.keys) subtyping.members

/-- Every function through which a constraint of `schema` reads the snapshot reads one table of
the schema: each foreign key's and mandatory participation's parents, each subtyping's supertype
and each member's keys.  Aligned with the schema's tables and subtypings, as nested tuples, so that
`schema_coherence%` builds an instance as one term, linear in the size of the schema. -/
class Coherent (schema : Schema Snapshot) where
  tables : HTuple (schema.TableReads) schema.tables
  subtypings : HTuple (schema.SubtypingReads) schema.subtypings

/-- The table that foreign key `j` of the table at `p` reads. -/
@[expose] def Coherent.foreignKey (coherent : schema.Coherent) (p : Fin schema.tables.length)
    (j : Fin schema.tables[p].table.foreignKeys.length) :
    schema.ReadsTable schema.tables[p].table.foreignKeys[j].parents :=
  (HTuple.get coherent.tables p).1.get j

/-- The table that mandatory participation `j` of the table at `p` reads. -/
@[expose] def Coherent.participation (coherent : schema.Coherent) (p : Fin schema.tables.length)
    (j : Fin schema.tables[p].table.participations.length) :
    schema.ReadsTable schema.tables[p].table.participations[j].parents :=
  (HTuple.get coherent.tables p).2.get j

/-- The table that the supertype of subtyping `k` reads. -/
@[expose] def Coherent.supertype (coherent : schema.Coherent) (k : Fin schema.subtypings.length) :
    schema.ReadsTable fun s ↦ (schema.subtypings[k].supertype.table.rows s).toRelation :=
  (HTuple.get coherent.subtypings k).1

/-- The table that the keys of member `m` of subtyping `k` read. -/
@[expose] def Coherent.member (coherent : schema.Coherent) (k : Fin schema.subtypings.length)
    (m : Fin schema.subtypings[k].members.length) :
    schema.ReadsTable schema.subtypings[k].members[m].keys :=
  (HTuple.get coherent.subtypings k).2.get m


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
probes the grown database at one key.  `refusal?` decides it from the database's indexes, in
O(d log n) time for d rows of the delta and n of the database, besides a pass over the schema's
tables and constraints. -/

/-- `delta` adds `row` to the table at `q`. -/
@[expose] def Added (delta : List (Insert schema)) (q : Fin schema.tables.length)
    (row : schema.tables[q].Row) : Prop :=
  ∃ insert ∈ delta, insert.rowAt q = some row

/-- No other row of a table of `next` shares a further unique key with a row the delta adds. -/
@[expose] def UniqueAccepted (delta : List (Insert schema)) (next : Snapshot) : Prop :=
  ∀ (q : Fin schema.tables.length) (row : schema.tables[q].Row), Added delta q row →
    ∀ unique : UniqueKey schema.tables[q].Row, unique ∈ schema.tables[q].table.uniqueKeys →
    ∀ other : schema.tables[q].Row, other ∈ schema.tables[q].table.rows next →
      unique.key other = unique.key row → other = row

/-- Every foreign key of a row the delta adds finds a parent in `next` that it may refer to. -/
@[expose] def ForeignAccepted (delta : List (Insert schema)) (next : Snapshot) : Prop :=
  ∀ (q : Fin schema.tables.length) (row : schema.tables[q].Row), Added delta q row →
    ∀ foreign : ForeignKey Snapshot schema.tables[q].Row, foreign ∈ schema.tables[q].table.foreignKeys →
    ∃ parent ∈ foreign.parents next,
      foreign.allowed row parent = true ∧ foreign.primary parent = foreign.reference row

/-- Every parent row the delta adds, in the scope of a mandatory participation, has a child in
`next`. -/
@[expose] def ParticipationAccepted [coherent : schema.Coherent] (delta : List (Insert schema))
    (next : Snapshot) : Prop :=
  ∀ (p : Fin schema.tables.length) (j : Fin schema.tables[p].table.participations.length) row,
    Added delta (coherent.participation p j).position row →
    schema.tables[p].table.participations[j].scope ((coherent.participation p j).conv row) = true →
    ∃ child : schema.tables[p].Row, child ∈ schema.tables[p].table.rows next ∧
      schema.tables[p].table.participations[j].reference child =
        schema.tables[p].table.participations[j].primary ((coherent.participation p j).conv row)

/-- Every row the delta adds to a subtype table has the key of a supertype row of `next` of one of
the member's facts, and its key is in no other member of `next`. -/
@[expose] def MemberAccepted [coherent : schema.Coherent] (delta : List (Insert schema))
    (next : Snapshot) : Prop :=
  ∀ (k : Fin schema.subtypings.length) (m : Fin schema.subtypings[k].members.length) row,
    Added delta (coherent.member k m).position row →
    (∃ parent : schema.subtypings[k].supertype.Row, parent ∈ schema.subtypings[k].supertype.table.rows next ∧
      schema.subtypings[k].supertype.key parent = (coherent.member k m).conv row ∧
        schema.subtypings[k].members[m].facts.Contains (schema.subtypings[k].fact parent)) ∧
    ∀ other : Fin schema.subtypings[k].members.length, other ≠ m →
      (coherent.member k m).conv row ∉ schema.subtypings[k].members[other].keys next

/-- Every supertype row the delta adds, in the scope of a covering or exhaustive subtyping, is in
some member of `next`. -/
@[expose] def CoverAccepted [coherent : schema.Coherent] (delta : List (Insert schema))
    (next : Snapshot) : Prop :=
  ∀ (k : Fin schema.subtypings.length) row, Added delta (coherent.supertype k).position row →
    schema.subtypings[k].inScope ((coherent.supertype k).conv row) = true →
    ∃ member : SubtypeMember Snapshot schema.subtypings[k].supertype.Key schema.subtypings[k].Fact,
      member ∈ schema.subtypings[k].members ∧
      schema.subtypings[k].supertype.key ((coherent.supertype k).conv row) ∈ member.keys next

variable (schema) in
/-- The delta's rows, applied as a set to `previous`, keep every primary key, further unique key,
foreign key, mandatory participation and subtyping, as far as a row they add can break it. -/
@[expose] def Accepts [schema.Coherent] (previous : Snapshot) (delta : List (Insert schema)) : Prop :=
  schema.KeysAgree previous delta ∧ UniqueAccepted delta (schema.applied previous delta) ∧
    ForeignAccepted delta (schema.applied previous delta) ∧
    ParticipationAccepted delta (schema.applied previous delta) ∧
    MemberAccepted delta (schema.applied previous delta) ∧ CoverAccepted delta (schema.applied previous delta)

/-! #### Deciding it -/

/-- The first of `rows`, new rows of the table at `q`, whose value of a further unique key another
row of the grown table has, through the table's indexes. -/
def uniqueClash? (indexes : schema.Indexes) (q : Fin schema.tables.length)
    (rows : List schema.tables[q].Row) : Option Violation :=
  rows.findSome? fun row ↦ (List.finRange schema.tables[q].table.uniqueKeys.length).findSome? fun j ↦
    if ((HTuple.get indexes q).1.get j).onlyAt (schema.tables[q].table.uniqueKeys[j].key row)
      (schema.tables[q].key row) then none
    else some (.duplicate schema.tables[q].table.name schema.tables[q].table.uniqueKeys[j].name)

/-- The first foreign key that a new row of the table at `q` breaks in `next`: `wrongKind` if it
finds a parent it may not refer to, and `dangling` if it finds none. -/
def foreignUnmatched? (next : Snapshot) (q : Fin schema.tables.length) (row : schema.tables[q].Row) :
    Option Violation :=
  (schema.tables[q].table.foreignKeys.find? fun foreign ↦ !foreign.holds (Relation.ofList [row]) next).map
    fun foreign ↦ if foreign.present (Relation.ofList [row]) next then
        .wrongKind schema.tables[q].table.name foreign.column
      else .dangling schema.tables[q].table.name foreign.column

/-- Whether the new row `row` of the parent table of participation `j` of the table at `p` lacks
a child, through the participation's index. -/
def participationUnmet? [coherent : schema.Coherent] (indexes : schema.Indexes) (p : Fin schema.tables.length)
    (j : Fin schema.tables[p].table.participations.length)
    (row : schema.tables[(coherent.participation p j).position].Row) : Option Violation :=
  if schema.tables[p].table.participations[j].scope ((coherent.participation p j).conv row) &&
      !((HTuple.get indexes p).2.get j).anyAt
        (schema.tables[p].table.participations[j].primary ((coherent.participation p j).conv row))
  then some (.missing schema.tables[p].table.name schema.tables[p].table.participations[j].column)
  else none

/-- The first member other than `m` of subtyping `k` that has the key `primary` in `next`, as an
overlap that names the two members in the order of the subtyping. -/
def memberOverlap? (next : Snapshot) (k : Fin schema.subtypings.length)
    (m : Fin schema.subtypings[k].members.length) (primary : schema.subtypings[k].supertype.Key) :
    Option Violation :=
  (List.finRange schema.subtypings[k].members.length).findSome? fun other ↦
    if other ≠ m ∧ schema.subtypings[k].members[other].has next primary = true then
      if other.val < m.val then
        some (.overlap schema.subtypings[k].name schema.subtypings[k].members[other].name
          schema.subtypings[k].members[m].name)
      else some (.overlap schema.subtypings[k].name schema.subtypings[k].members[m].name
          schema.subtypings[k].members[other].name)
    else none

/-- What is wrong in `next` with the key `primary` of a new row of member `m` of subtyping `k`:
no supertype row has it (`orphan`), the supertype row is of another fact (`wrongFact`), or another
member has it (`overlap`). -/
def memberMisfit? (next : Snapshot) (k : Fin schema.subtypings.length)
    (m : Fin schema.subtypings[k].members.length) (primary : schema.subtypings[k].supertype.Key) :
    Option Violation :=
  ((schema.subtypings[k].supertype.table.rows next).find? primary).elim
    (some (.orphan schema.subtypings[k].name schema.subtypings[k].members[m].name)) fun parent ↦
    if schema.subtypings[k].members[m].facts.contains (schema.subtypings[k].fact parent) then
      memberOverlap? next k m primary
    else some (.wrongFact schema.subtypings[k].name schema.subtypings[k].members[m].name)

/-- Whether the new supertype row `row` of subtyping `k` is in scope and in no member of `next`. -/
def uncovered? (next : Snapshot) (k : Fin schema.subtypings.length) (row : schema.subtypings[k].supertype.Row) :
    Option Violation :=
  if schema.subtypings[k].inScope row &&
      !(schema.subtypings[k].members.any fun member ↦
        member.has next (schema.subtypings[k].supertype.key row))
  then some (.uncovered schema.subtypings[k].name (schema.subtypings[k].members.map (·.name)))
  else none

variable (schema) in
/-- The first constraint that a row the delta adds breaks in `next`, the grown database, whose
indexes are `indexes`, in the order: further unique keys, foreign keys, mandatory participations,
subtype members, coverage. -/
def deltaRefusal? [coherent : schema.Coherent] (delta : List (Insert schema)) (next : Snapshot)
    (indexes : schema.Indexes) : Option Violation :=
  let groups := schema.grouped delta
  ((List.finRange schema.tables.length).findSome? fun q ↦ uniqueClash? indexes q (rowsAt groups q)).or <|
  ((List.finRange schema.tables.length).findSome? fun q ↦
    (rowsAt groups q).findSome? (foreignUnmatched? next q)).or <|
  ((List.finRange schema.tables.length).findSome? fun p ↦
    (List.finRange schema.tables[p].table.participations.length).findSome? fun j ↦
      (rowsAt groups (coherent.participation p j).position).findSome? (participationUnmet? indexes p j)).or <|
  ((List.finRange schema.subtypings.length).findSome? fun k ↦
    (List.finRange schema.subtypings[k].members.length).findSome? fun m ↦
      (rowsAt groups (coherent.member k m).position).findSome? fun row ↦
        memberMisfit? next k m ((coherent.member k m).conv row)).or <|
  (List.finRange schema.subtypings.length).findSome? fun k ↦
    (rowsAt groups (coherent.supertype k).position).findSome? fun row ↦
      uncovered? next k ((coherent.supertype k).conv row)

variable (schema) in
/-- Why appending `delta` to `previous` is refused, given the grown database `next` and its
indexes: a primary key conflict first, then the first constraint a new row breaks. -/
def refusal? [schema.Coherent] (previous : Snapshot) (delta : List (Insert schema)) (next : Snapshot)
    (indexes : schema.Indexes) : Option Refusal :=
  match schema.firstConflict? previous delta with
  | some refusal => some refusal
  | none => (schema.deltaRefusal? delta next indexes).map .invalid

/-! #### What the decision means -/

theorem Appended.mem_of_added {previous next : Snapshot} {delta : List (Insert schema)}
    (appended : schema.Appended previous delta next) {q : Fin schema.tables.length}
    {row : schema.tables[q].Row} (added : Added delta q row) : row ∈ schema.tables[q].table.rows next :=
  (appended q row).mpr (Or.inr added)

theorem onlyAt_iff_unique {next : Snapshot} {indexes : schema.Indexes} {q : Fin schema.tables.length}
    {row : schema.tables[q].Row} (inNext : row ∈ schema.tables[q].table.rows next)
    (agrees : (HTuple.get indexes q).Agrees (schema.tables[q].table.rows next))
    (j : Fin schema.tables[q].table.uniqueKeys.length) :
    ((HTuple.get indexes q).1.get j).onlyAt (schema.tables[q].table.uniqueKeys[j].key row)
        (schema.tables[q].key row) = true ↔
      ∀ other : schema.tables[q].Row, other ∈ schema.tables[q].table.rows next →
        schema.tables[q].table.uniqueKeys[j].key other = schema.tables[q].table.uniqueKeys[j].key row →
          other = row := by
  rw [Index.onlyAt_iff]
  constructor
  · intro only other member same
    exact Rows.key_injective member inNext (only _ ((agrees.1 j _ _).mpr ⟨other, member, rfl, same⟩))
  · intro unique other listed
    obtain ⟨found, member, rfl, same⟩ := (agrees.1 j _ _).mp listed
    rw [unique found member same]

/-- The unique-key probe of one new row finds nothing exactly when no other row shares a further
unique key with it. -/
theorem uniqueProbe_eq_none {next : Snapshot} {indexes : schema.Indexes} {q : Fin schema.tables.length}
    {row : schema.tables[q].Row} (inNext : row ∈ schema.tables[q].table.rows next)
    (agrees : (HTuple.get indexes q).Agrees (schema.tables[q].table.rows next)) :
    ((List.finRange schema.tables[q].table.uniqueKeys.length).findSome? fun j ↦
      if ((HTuple.get indexes q).1.get j).onlyAt (schema.tables[q].table.uniqueKeys[j].key row)
        (schema.tables[q].key row) then none
      else some (Violation.duplicate schema.tables[q].table.name schema.tables[q].table.uniqueKeys[j].name)) =
        none ↔
      ∀ unique : UniqueKey schema.tables[q].Row, unique ∈ schema.tables[q].table.uniqueKeys →
        ∀ other : schema.tables[q].Row, other ∈ schema.tables[q].table.rows next →
          unique.key other = unique.key row → other = row := by
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro none unique member
    obtain ⟨j, bound, rfl⟩ := List.getElem_of_mem member
    have probe := none ⟨j, bound⟩ (List.mem_finRange _)
    split at probe
    · rename_i only
      exact (onlyAt_iff_unique inNext agrees ⟨j, bound⟩).mp only
    · cases probe
  · intro unique j _
    rw [ite_eq_left ((onlyAt_iff_unique inNext agrees j).mpr (unique _ (List.getElem_mem j.isLt)))]

theorem uniqueProbe_sound {next : Snapshot} {indexes : schema.Indexes} {q : Fin schema.tables.length}
    {row : schema.tables[q].Row} (inNext : row ∈ schema.tables[q].table.rows next)
    (agrees : (HTuple.get indexes q).Agrees (schema.tables[q].table.rows next)) {violation : Violation}
    (found : ((List.finRange schema.tables[q].table.uniqueKeys.length).findSome? fun j ↦
      if ((HTuple.get indexes q).1.get j).onlyAt (schema.tables[q].table.uniqueKeys[j].key row)
        (schema.tables[q].key row) then none
      else some (Violation.duplicate schema.tables[q].table.name schema.tables[q].table.uniqueKeys[j].name)) =
        some violation) :
    schema.Violated next violation := by
  obtain ⟨j, _, found⟩ := List.exists_of_findSome?_eq_some found
  split at found
  · cases found
  · rename_i clash
    cases found
    have : ¬ ∀ other : schema.tables[q].Row, other ∈ schema.tables[q].table.rows next →
        schema.tables[q].table.uniqueKeys[j].key other = schema.tables[q].table.uniqueKeys[j].key row →
          other = row :=
      fun unique ↦ clash ((onlyAt_iff_unique inNext agrees j).mpr unique)
    simp only [Classical.not_forall] at this
    obtain ⟨other, member, same, differs⟩ := this
    exact ⟨schema.tables[q], List.getElem_mem q.isLt, rfl, schema.tables[q].table.uniqueKeys[j],
      List.getElem_mem j.isLt, rfl, fun keyed ↦ differs (keyed.eq_of_key (Rows.mem_toRelation.mpr member)
        (Rows.mem_toRelation.mpr inNext) same)⟩

theorem uniqueClashes_eq_none {previous next : Snapshot} {delta : List (Insert schema)}
    {indexes : schema.Indexes} (appended : schema.Appended previous delta next)
    (agree : schema.IndexesAgree next indexes) :
    ((List.finRange schema.tables.length).findSome? fun q ↦
      uniqueClash? indexes q (rowsAt (schema.grouped delta) q)) = none ↔ UniqueAccepted delta next := by
  simp only [List.findSome?_eq_none_iff, List.mem_finRange, true_implies, uniqueClash?]
  constructor
  · intro none q row added
    exact (uniqueProbe_eq_none (appended.mem_of_added added) (agree q)).mp
      (List.findSome?_eq_none_iff.mpr fun j _ ↦ none q row (mem_rowsAt.mpr added) j)
  · intro unique q row member j
    exact List.findSome?_eq_none_iff.mp ((uniqueProbe_eq_none (appended.mem_of_added
      (mem_rowsAt.mp member)) (agree q)).mpr (unique q row (mem_rowsAt.mp member))) j (List.mem_finRange j)

theorem uniqueClashes_sound {previous next : Snapshot} {delta : List (Insert schema)}
    {indexes : schema.Indexes} (appended : schema.Appended previous delta next)
    (agree : schema.IndexesAgree next indexes) {violation : Violation}
    (found : ((List.finRange schema.tables.length).findSome? fun q ↦
      uniqueClash? indexes q (rowsAt (schema.grouped delta) q)) = some violation) :
    schema.Violated next violation := by
  obtain ⟨q, _, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨row, member, found⟩ := List.exists_of_findSome?_eq_some found
  exact uniqueProbe_sound (appended.mem_of_added (mem_rowsAt.mp member)) (agree q) found

theorem foreignUnmatched?_eq_none {next : Snapshot} {q : Fin schema.tables.length}
    {row : schema.tables[q].Row} :
    foreignUnmatched? next q row = none ↔
      ∀ foreign : ForeignKey Snapshot schema.tables[q].Row, foreign ∈ schema.tables[q].table.foreignKeys →
        ∃ parent ∈ foreign.parents next, foreign.allowed row parent = true ∧
          foreign.primary parent = foreign.reference row := by
  simp only [foreignUnmatched?, Option.map_eq_none_iff, List.find?_eq_none, Bool.not_eq_true',
    Bool.not_eq_false, ForeignKey.holds_iff, Relation.mem_ofList, List.mem_singleton, forall_eq]

theorem foreignUnmatched?_sound {next : Snapshot} {q : Fin schema.tables.length}
    {row : schema.tables[q].Row} (inNext : row ∈ schema.tables[q].table.rows next) {violation : Violation}
    (found : foreignUnmatched? next q row = some violation) : schema.Violated next violation := by
  obtain ⟨foreign, first, rfl⟩ := Option.map_eq_some_iff.mp found
  have member := List.mem_of_find?_eq_some first
  have broken := List.find?_some first
  simp only [Bool.not_eq_true', ← Bool.not_eq_true, ForeignKey.holds_iff, Relation.mem_ofList,
    List.mem_singleton, forall_eq] at broken
  split
  · rename_i present
    rw [foreign.present_iff] at present
    obtain ⟨parent, parentMember, same⟩ := present row (Relation.mem_ofList.mpr (List.mem_singleton_self row))
    exact ⟨schema.tables[q], List.getElem_mem q.isLt, rfl, foreign, member, rfl, row, inNext,
      ⟨parent, parentMember, same⟩, broken⟩
  · rename_i absent
    refine ⟨schema.tables[q], List.getElem_mem q.isLt, rfl, foreign, member, rfl, row, inNext, ?_⟩
    rintro ⟨parent, parentMember, same⟩
    refine absent ((foreign.present_iff _ _).mpr fun child inside ↦ ?_)
    rw [Relation.mem_ofList, List.mem_singleton] at inside
    subst inside
    exact ⟨parent, parentMember, same⟩

theorem foreignUnmatches_eq_none {next : Snapshot} {delta : List (Insert schema)} :
    ((List.finRange schema.tables.length).findSome? fun q ↦
      (rowsAt (schema.grouped delta) q).findSome? (foreignUnmatched? next q)) = none ↔
      ForeignAccepted delta next := by
  simp only [List.findSome?_eq_none_iff, List.mem_finRange, true_implies, foreignUnmatched?_eq_none]
  exact ⟨fun none q row added ↦ none q row (mem_rowsAt.mpr added),
    fun holds q row member ↦ holds q row (mem_rowsAt.mp member)⟩

theorem foreignUnmatches_sound {previous next : Snapshot} {delta : List (Insert schema)}
    (appended : schema.Appended previous delta next) {violation : Violation}
    (found : ((List.finRange schema.tables.length).findSome? fun q ↦
      (rowsAt (schema.grouped delta) q).findSome? (foreignUnmatched? next q)) = some violation) :
    schema.Violated next violation := by
  obtain ⟨q, _, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨row, member, found⟩ := List.exists_of_findSome?_eq_some found
  exact foreignUnmatched?_sound (appended.mem_of_added (mem_rowsAt.mp member)) found

theorem participationUnmet?_eq_none [coherent : schema.Coherent] {next : Snapshot}
    {indexes : schema.Indexes} {p : Fin schema.tables.length}
    (agrees : (HTuple.get indexes p).Agrees (schema.tables[p].table.rows next))
    {j : Fin schema.tables[p].table.participations.length}
    {row : schema.tables[(coherent.participation p j).position].Row} :
    participationUnmet? indexes p j row = none ↔
      (schema.tables[p].table.participations[j].scope ((coherent.participation p j).conv row) = true →
        ∃ child : schema.tables[p].Row, child ∈ schema.tables[p].table.rows next ∧
          schema.tables[p].table.participations[j].reference child =
            schema.tables[p].table.participations[j].primary ((coherent.participation p j).conv row)) := by
  unfold participationUnmet?
  have listed : ∀ value, ((HTuple.get indexes p).2.get j).anyAt value = true ↔
      ∃ child : schema.tables[p].Row, child ∈ schema.tables[p].table.rows next ∧
        schema.tables[p].table.participations[j].reference child = value := by
    intro value
    rw [Index.anyAt_iff]
    constructor
    · rintro ⟨primary, inside⟩
      obtain ⟨child, member, _, same⟩ := (agrees.2 j _ _).mp inside
      exact ⟨child, member, same⟩
    · rintro ⟨child, member, same⟩
      exact ⟨_, (agrees.2 j _ _).mpr ⟨child, member, rfl, same⟩⟩
  split
  · rename_i unmet
    simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, listed] at unmet
    simp only [reduceCtorEq, false_iff, Classical.not_imp]
    exact unmet
  · rename_i met
    simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, listed, not_and,
      Classical.not_not] at met
    simp only [true_iff]
    exact met

theorem participationUnmet?_sound [coherent : schema.Coherent] {next : Snapshot}
    {indexes : schema.Indexes} {p : Fin schema.tables.length}
    (agrees : (HTuple.get indexes p).Agrees (schema.tables[p].table.rows next))
    {j : Fin schema.tables[p].table.participations.length}
    {row : schema.tables[(coherent.participation p j).position].Row}
    (inNext : row ∈ schema.tables[(coherent.participation p j).position].table.rows next)
    {violation : Violation} (found : participationUnmet? indexes p j row = some violation) :
    schema.Violated next violation := by
  have unmet : participationUnmet? indexes p j row ≠ none := by rw [found]; exact Option.some_ne_none _
  rw [ne_eq, participationUnmet?_eq_none agrees, Classical.not_imp] at unmet
  obtain ⟨inScope, none⟩ := unmet
  unfold participationUnmet? at found
  split at found
  · cases found
    refine ⟨schema.tables[p], List.getElem_mem p.isLt, rfl, schema.tables[p].table.participations[j],
      List.getElem_mem j.isLt, rfl, (coherent.participation p j).conv row,
      ((coherent.participation p j).mem_iff next _).mpr ⟨row, inNext, rfl⟩, inScope, ?_⟩
    rintro ⟨child, member, same⟩
    exact none ⟨child, member, same⟩
  · cases found

theorem participationUnmets_eq_none [coherent : schema.Coherent] {next : Snapshot}
    {delta : List (Insert schema)} {indexes : schema.Indexes} (agree : schema.IndexesAgree next indexes) :
    ((List.finRange schema.tables.length).findSome? fun p ↦
      (List.finRange schema.tables[p].table.participations.length).findSome? fun j ↦
        (rowsAt (schema.grouped delta) (coherent.participation p j).position).findSome?
          (participationUnmet? indexes p j)) = none ↔ ParticipationAccepted delta next := by
  simp only [List.findSome?_eq_none_iff, List.mem_finRange, true_implies]
  constructor
  · intro none p j row added
    exact (participationUnmet?_eq_none (agree p)).mp (none p j row (mem_rowsAt.mpr added))
  · intro holds p j row member
    exact (participationUnmet?_eq_none (agree p)).mpr (holds p j row (mem_rowsAt.mp member))

theorem participationUnmets_sound [coherent : schema.Coherent] {previous next : Snapshot}
    {delta : List (Insert schema)} {indexes : schema.Indexes} (appended : schema.Appended previous delta next)
    (agree : schema.IndexesAgree next indexes) {violation : Violation}
    (found : ((List.finRange schema.tables.length).findSome? fun p ↦
      (List.finRange schema.tables[p].table.participations.length).findSome? fun j ↦
        (rowsAt (schema.grouped delta) (coherent.participation p j).position).findSome?
          (participationUnmet? indexes p j)) = some violation) :
    schema.Violated next violation := by
  obtain ⟨p, _, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨j, _, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨row, member, found⟩ := List.exists_of_findSome?_eq_some found
  exact participationUnmet?_sound (agree p) (appended.mem_of_added (mem_rowsAt.mp member)) found

/-- Two elements of a list, in their order in it, are a sublist of it. -/
theorem _root_.List.pair_sublist {α : Type u} :
    ∀ {l : List α} {i j : Nat} (first : i < l.length) (second : j < l.length), i < j → [l[i], l[j]].Sublist l
  | _ :: _, 0, _ + 1, _, _, _ => List.Sublist.cons_cons _ (List.singleton_sublist.mpr (List.getElem_mem _))
  | _ :: rest, _ + 1, _ + 1, first, second, before =>
    List.Sublist.cons _ (List.pair_sublist (l := rest) (Nat.lt_of_succ_lt_succ first)
      (Nat.lt_of_succ_lt_succ second) (Nat.lt_of_succ_lt_succ before))
  | _, _, 0, _, _, before => absurd before (Nat.not_lt_zero _)

theorem memberOverlap?_eq_none {next : Snapshot} {k : Fin schema.subtypings.length}
    {m : Fin schema.subtypings[k].members.length} {primary : schema.subtypings[k].supertype.Key} :
    memberOverlap? next k m primary = none ↔
      ∀ other : Fin schema.subtypings[k].members.length, other ≠ m →
        primary ∉ schema.subtypings[k].members[other].keys next := by
  unfold memberOverlap?
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro none other differs inside
    have probe := none other (List.mem_finRange other)
    rw [ite_eq_left ⟨differs, (schema.subtypings[k].members[other].has_iff next primary).mpr inside⟩] at probe
    split at probe <;> cases probe
  · intro apart other _
    rw [ite_eq_right fun ⟨differs, has⟩ ↦
      apart other differs ((schema.subtypings[k].members[other].has_iff next primary).mp has)]

theorem memberOverlap?_sound {next : Snapshot} {k : Fin schema.subtypings.length}
    {m : Fin schema.subtypings[k].members.length} {primary : schema.subtypings[k].supertype.Key}
    (inside : primary ∈ schema.subtypings[k].members[m].keys next) {violation : Violation}
    (found : memberOverlap? next k m primary = some violation) : schema.Violated next violation := by
  obtain ⟨other, _, found⟩ := List.exists_of_findSome?_eq_some found
  split at found
  · rename_i overlapping
    obtain ⟨differs, has⟩ := overlapping
    have also := (schema.subtypings[k].members[other].has_iff next primary).mp has
    split at found
    · rename_i before
      cases found
      exact ⟨schema.subtypings[k], List.getElem_mem k.isLt, rfl, schema.subtypings[k].members[other],
        schema.subtypings[k].members[m], List.pair_sublist other.isLt m.isLt before, rfl, rfl,
        fun apart ↦ apart primary also inside⟩
    · rename_i after
      cases found
      have before : m.val < other.val := by
        have : other.val ≠ m.val := fun same ↦ differs (Fin.ext same)
        omega
      exact ⟨schema.subtypings[k], List.getElem_mem k.isLt, rfl, schema.subtypings[k].members[m],
        schema.subtypings[k].members[other], List.pair_sublist m.isLt other.isLt before, rfl, rfl,
        fun apart ↦ apart primary inside also⟩
  · cases found

theorem memberMisfit?_eq_none {next : Snapshot} {k : Fin schema.subtypings.length}
    {m : Fin schema.subtypings[k].members.length} {primary : schema.subtypings[k].supertype.Key} :
    memberMisfit? next k m primary = none ↔
      (∃ parent : schema.subtypings[k].supertype.Row,
        parent ∈ schema.subtypings[k].supertype.table.rows next ∧
        schema.subtypings[k].supertype.key parent = primary ∧
          schema.subtypings[k].members[m].facts.Contains (schema.subtypings[k].fact parent)) ∧
      ∀ other : Fin schema.subtypings[k].members.length, other ≠ m →
        primary ∉ schema.subtypings[k].members[other].keys next := by
  unfold memberMisfit?
  cases found : (schema.subtypings[k].supertype.table.rows next).find? primary with
  | none =>
    simp only [Option.elim_none, reduceCtorEq, false_iff, not_and]
    rintro ⟨parent, member, same, _⟩
    exact absurd same (Rows.find?_eq_none.mp found parent member)
  | some parent =>
    obtain ⟨member, same⟩ := Rows.find?_eq_some.mp found
    simp only [Option.elim_some]
    split
    · rename_i fits
      rw [memberOverlap?_eq_none]
      exact ⟨fun apart ↦ ⟨⟨parent, member, same, FactSet.contains_iff.mp fits⟩, apart⟩, fun ⟨_, apart⟩ ↦ apart⟩
    · rename_i misfits
      simp only [reduceCtorEq, false_iff, not_and]
      rintro ⟨other, otherMember, otherSame, fits⟩
      have equal := Rows.key_injective otherMember member (otherSame.trans same.symm)
      subst equal
      exact absurd (FactSet.contains_iff.mpr fits) misfits

theorem memberMisfit?_sound {next : Snapshot} {k : Fin schema.subtypings.length}
    {m : Fin schema.subtypings[k].members.length} {primary : schema.subtypings[k].supertype.Key}
    (inside : primary ∈ schema.subtypings[k].members[m].keys next) {violation : Violation}
    (found : memberMisfit? next k m primary = some violation) : schema.Violated next violation := by
  unfold memberMisfit? at found
  cases lookup : (schema.subtypings[k].supertype.table.rows next).find? primary with
  | none =>
    rw [lookup, Option.elim_none] at found
    cases found
    exact ⟨schema.subtypings[k], List.getElem_mem k.isLt, rfl, schema.subtypings[k].members[m],
      List.getElem_mem m.isLt, rfl, primary, inside, Rows.find?_eq_none.mp lookup⟩
  | some parent =>
    obtain ⟨member, same⟩ := Rows.find?_eq_some.mp lookup
    rw [lookup, Option.elim_some] at found
    split at found
    · exact memberOverlap?_sound inside found
    · rename_i misfits
      cases found
      exact ⟨schema.subtypings[k], List.getElem_mem k.isLt, rfl, schema.subtypings[k].members[m],
        List.getElem_mem m.isLt, rfl, primary, inside, parent, member, same,
        fun fits ↦ misfits (FactSet.contains_iff.mpr fits)⟩

theorem uncovered?_eq_none {next : Snapshot} {k : Fin schema.subtypings.length}
    {row : schema.subtypings[k].supertype.Row} :
    uncovered? next k row = none ↔
      (schema.subtypings[k].inScope row = true →
        ∃ member : SubtypeMember Snapshot schema.subtypings[k].supertype.Key schema.subtypings[k].Fact,
          member ∈ schema.subtypings[k].members ∧
          schema.subtypings[k].supertype.key row ∈ member.keys next) := by
  unfold uncovered?
  have some_iff : (schema.subtypings[k].members.any fun member ↦
      member.has next (schema.subtypings[k].supertype.key row)) = true ↔
      ∃ member : SubtypeMember Snapshot schema.subtypings[k].supertype.Key schema.subtypings[k].Fact,
        member ∈ schema.subtypings[k].members ∧
        schema.subtypings[k].supertype.key row ∈ member.keys next := by
    rw [List.any_eq_true]
    exact exists_congr fun member ↦ and_congr_right fun _ ↦ member.has_iff next _
  split
  · rename_i bad
    simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, some_iff] at bad
    simp only [reduceCtorEq, false_iff, Classical.not_imp]
    exact bad
  · rename_i good
    simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, some_iff, not_and,
      Classical.not_not] at good
    simp only [true_iff]
    exact good

theorem uncovered?_sound {next : Snapshot} {k : Fin schema.subtypings.length}
    {row : schema.subtypings[k].supertype.Row}
    (inNext : row ∈ schema.subtypings[k].supertype.table.rows next) {violation : Violation}
    (found : uncovered? next k row = some violation) : schema.Violated next violation := by
  have bad : uncovered? next k row ≠ none := by rw [found]; exact Option.some_ne_none _
  rw [ne_eq, uncovered?_eq_none, Classical.not_imp] at bad
  obtain ⟨inScope, none⟩ := bad
  unfold uncovered? at found
  split at found
  · cases found
    refine ⟨schema.subtypings[k], List.getElem_mem k.isLt, rfl, rfl, schema.subtypings[k].supertype.key row,
      ?_, fun member inMembers inKeys ↦ none ⟨member, inMembers, inKeys⟩⟩
    simp only [Subtyping.covered, Relation.mem_project, Relation.mem_select, Rows.mem_toRelation]
    exact ⟨row, ⟨inNext, inScope⟩, rfl⟩
  · cases found

/-- A member key that a table-reading function reads in `next` from a row the delta adds. -/
theorem ReadsTable.mem_of_added {X : Type} {read : Snapshot → Relation X} (reads : schema.ReadsTable read)
    {previous next : Snapshot} {delta : List (Insert schema)} (appended : schema.Appended previous delta next)
    {row : schema.tables[reads.position].Row} (added : Added delta reads.position row) :
    reads.conv row ∈ read next :=
  (reads.mem_iff next _).mpr ⟨row, appended.mem_of_added added, rfl⟩

theorem memberMisfits_eq_none [coherent : schema.Coherent] {next : Snapshot}
    {delta : List (Insert schema)} :
    ((List.finRange schema.subtypings.length).findSome? fun k ↦
      (List.finRange schema.subtypings[k].members.length).findSome? fun m ↦
        (rowsAt (schema.grouped delta) (coherent.member k m).position).findSome? fun row ↦
          memberMisfit? next k m ((coherent.member k m).conv row)) = none ↔ MemberAccepted delta next := by
  simp only [List.findSome?_eq_none_iff, List.mem_finRange, true_implies, memberMisfit?_eq_none]
  exact ⟨fun none k m row added ↦ none k m row (mem_rowsAt.mpr added),
    fun holds k m row member ↦ holds k m row (mem_rowsAt.mp member)⟩

theorem memberMisfits_sound [coherent : schema.Coherent] {previous next : Snapshot}
    {delta : List (Insert schema)} (appended : schema.Appended previous delta next) {violation : Violation}
    (found : ((List.finRange schema.subtypings.length).findSome? fun k ↦
      (List.finRange schema.subtypings[k].members.length).findSome? fun m ↦
        (rowsAt (schema.grouped delta) (coherent.member k m).position).findSome? fun row ↦
          memberMisfit? next k m ((coherent.member k m).conv row)) = some violation) :
    schema.Violated next violation := by
  obtain ⟨k, _, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨m, _, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨row, member, found⟩ := List.exists_of_findSome?_eq_some found
  exact memberMisfit?_sound ((coherent.member k m).mem_of_added appended (mem_rowsAt.mp member)) found

theorem uncovereds_eq_none [coherent : schema.Coherent] {next : Snapshot} {delta : List (Insert schema)} :
    ((List.finRange schema.subtypings.length).findSome? fun k ↦
      (rowsAt (schema.grouped delta) (coherent.supertype k).position).findSome? fun row ↦
        uncovered? next k ((coherent.supertype k).conv row)) = none ↔ CoverAccepted delta next := by
  simp only [List.findSome?_eq_none_iff, List.mem_finRange, true_implies, uncovered?_eq_none]
  exact ⟨fun none k row added ↦ none k row (mem_rowsAt.mpr added),
    fun holds k row member ↦ holds k row (mem_rowsAt.mp member)⟩

theorem uncovereds_sound [coherent : schema.Coherent] {previous next : Snapshot}
    {delta : List (Insert schema)} (appended : schema.Appended previous delta next) {violation : Violation}
    (found : ((List.finRange schema.subtypings.length).findSome? fun k ↦
      (rowsAt (schema.grouped delta) (coherent.supertype k).position).findSome? fun row ↦
        uncovered? next k ((coherent.supertype k).conv row)) = some violation) :
    schema.Violated next violation := by
  obtain ⟨k, _, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨row, member, found⟩ := List.exists_of_findSome?_eq_some found
  exact uncovered?_sound (Rows.mem_toRelation.mp
    ((coherent.supertype k).mem_of_added appended (mem_rowsAt.mp member))) found

theorem deltaRefusal?_eq_none [schema.Coherent] {previous next : Snapshot} {delta : List (Insert schema)}
    {indexes : schema.Indexes} (appended : schema.Appended previous delta next)
    (agree : schema.IndexesAgree next indexes) :
    schema.deltaRefusal? delta next indexes = none ↔
      UniqueAccepted delta next ∧ ForeignAccepted delta next ∧ ParticipationAccepted delta next ∧
        MemberAccepted delta next ∧ CoverAccepted delta next := by
  simp only [deltaRefusal?, Option.or_eq_none_iff]
  rw [uniqueClashes_eq_none appended agree, foreignUnmatches_eq_none, participationUnmets_eq_none agree,
    memberMisfits_eq_none, uncovereds_eq_none]

theorem deltaRefusal?_sound [schema.Coherent] {previous next : Snapshot} {delta : List (Insert schema)}
    {indexes : schema.Indexes} (appended : schema.Appended previous delta next)
    (agree : schema.IndexesAgree next indexes) {violation : Violation}
    (found : schema.deltaRefusal? delta next indexes = some violation) : schema.Violated next violation := by
  simp only [deltaRefusal?, Option.or_eq_some_iff] at found
  rcases found with unique | ⟨_, foreign | ⟨_, participation | ⟨_, member | ⟨_, cover⟩⟩⟩⟩
  · exact uniqueClashes_sound appended agree unique
  · exact foreignUnmatches_sound appended foreign
  · exact participationUnmets_sound appended agree participation
  · exact memberMisfits_sound appended member
  · exact uncovereds_sound appended cover

/-- With the grown database's indexes, `refusal?` finds nothing exactly when the delta is
accepted. -/
theorem refusal?_eq_none [schema.Wiring] [schema.Coherent] {previous : Snapshot} {delta : List (Insert schema)}
    {indexes : schema.Indexes} (agree : schema.IndexesAgree (schema.applied previous delta) indexes) :
    schema.refusal? previous delta (schema.applied previous delta) indexes = none ↔
      schema.Accepts previous delta := by
  unfold refusal?
  split
  · rename_i conflict
    simp only [reduceCtorEq, false_iff]
    intro accepts
    rw [firstConflict?_eq_none_of_keysAgree accepts.1] at conflict
    cases conflict
  · rename_i none
    have agreeKeys := keysAgree_of_firstConflict?_eq_none none
    rw [Option.map_eq_none_iff, deltaRefusal?_eq_none (appended_of_keysAgree agreeKeys) agree]
    exact ⟨fun holds ↦ ⟨agreeKeys, holds⟩, fun accepts ↦ accepts.2⟩

/-- Every refusal that `refusal?` gives, with the grown database's indexes, is refused for the
reason it gives: a primary key conflict, or a violation of the grown database. -/
theorem refusal?_sound [schema.Wiring] [schema.Coherent] {previous : Snapshot} {delta : List (Insert schema)}
    {indexes : schema.Indexes} (agree : schema.IndexesAgree (schema.applied previous delta) indexes)
    {refusal : Refusal} (found : schema.refusal? previous delta (schema.applied previous delta) indexes = some refusal) :
    schema.Refuses previous delta refusal := by
  unfold refusal? at found
  split at found
  · rename_i conflict
    cases found
    exact firstConflict?_sound conflict
  · rename_i none
    obtain ⟨violation, inner, rfl⟩ := Option.map_eq_some_iff.mp found
    exact deltaRefusal?_sound (appended_of_keysAgree (keysAgree_of_firstConflict?_eq_none none)) agree inner

/-! #### The incremental check accepts what the full check accepts -/

/-- A row of a table of `next` after `delta` is appended to `previous`: one of `previous`, or one
the delta adds. -/
theorem Appended.old_or_added {previous next : Snapshot} {delta : List (Insert schema)}
    (appended : schema.Appended previous delta next) {q : Fin schema.tables.length}
    {row : schema.tables[q].Row} (member : row ∈ schema.tables[q].table.rows next) :
    row ∈ schema.tables[q].table.rows previous ∨ Added delta q row :=
  (appended q row).mp member

/-- A valid database with a delta appended, which the delta's rows accept, is valid. -/
theorem valid_of_accepts [schema.Wiring] [coherent : schema.Coherent] {previous : Snapshot}
    {delta : List (Insert schema)} (valid : schema.Valid previous) (accepts : schema.Accepts previous delta) :
    schema.Valid (schema.applied previous delta) := by
  obtain ⟨keys, foreignKeys, typed, participations, disjoint, covered, indexed⟩ := valid
  obtain ⟨agreeKeys, unique, foreign, participation, memberOk, cover⟩ := accepts
  have appended := appended_of_keysAgree agreeKeys
  have grown := appended.extends
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, indexed.applied delta⟩
  · -- further unique keys
    intro entry member uniqueKey uniqueMember
    obtain ⟨q, bound, rfl⟩ := List.getElem_of_mem member
    refine Relation.keyed_iff_mem.mpr ⟨Rows.toRelation_distinct, fun left leftMember right rightMember same ↦ ?_⟩
    have leftIn := Rows.mem_toRelation.mp leftMember
    have rightIn := Rows.mem_toRelation.mp rightMember
    rcases appended.old_or_added (q := ⟨q, bound⟩) leftIn with leftOld | leftAdded
    · rcases appended.old_or_added (q := ⟨q, bound⟩) rightIn with rightOld | rightAdded
      · exact (keys _ member uniqueKey uniqueMember).eq_of_key (Rows.mem_toRelation.mpr leftOld)
          (Rows.mem_toRelation.mpr rightOld) same
      · exact unique ⟨q, bound⟩ right rightAdded uniqueKey uniqueMember left leftIn same
    · exact (unique ⟨q, bound⟩ left leftAdded uniqueKey uniqueMember right rightIn same.symm).symm
  · -- foreign keys
    intro entry member foreignKey foreignMember child childMember
    obtain ⟨q, bound, rfl⟩ := List.getElem_of_mem member
    rcases appended.old_or_added (q := ⟨q, bound⟩) (Rows.mem_toRelation.mp childMember) with old | added
    · obtain ⟨j, jBound, rfl⟩ := List.getElem_of_mem foreignMember
      obtain ⟨parent, parentMember, allowed, same⟩ :=
        foreignKeys _ member _ foreignMember child (Rows.mem_toRelation.mpr old)
      exact ⟨parent, (coherent.foreignKey ⟨q, bound⟩ ⟨j, jBound⟩).mono grown parentMember, allowed, same⟩
    · exact foreign ⟨q, bound⟩ child added foreignKey foreignMember
  · -- subtype members are typed
    intro subtyping member memberEntry memberMember primary inside
    obtain ⟨k, bound, rfl⟩ := List.getElem_of_mem member
    obtain ⟨m, mBound, rfl⟩ := List.getElem_of_mem memberMember
    rcases ((coherent.member ⟨k, bound⟩ ⟨m, mBound⟩).mem_appended appended primary).mp inside with
      old | ⟨insert, inDelta, row, found, rfl⟩
    · obtain ⟨parent, parentMember, same, fits⟩ := typed _ member _ memberMember primary old
      refine ⟨parent, ?_, same, fits⟩
      exact Rows.mem_toRelation.mp ((coherent.supertype ⟨k, bound⟩).mono grown
        (Rows.mem_toRelation.mpr parentMember))
    · exact (memberOk ⟨k, bound⟩ ⟨m, mBound⟩ row ⟨insert, inDelta, found⟩).1
  · -- mandatory participations
    intro entry member participationEntry participationMember parent parentMember inScope
    obtain ⟨p, bound, rfl⟩ := List.getElem_of_mem member
    obtain ⟨j, jBound, rfl⟩ := List.getElem_of_mem participationMember
    rcases ((coherent.participation ⟨p, bound⟩ ⟨j, jBound⟩).mem_appended appended parent).mp parentMember with
      old | ⟨insert, inDelta, row, found, rfl⟩
    · obtain ⟨child, childMember, same⟩ :=
        participations _ member _ participationMember parent old inScope
      exact ⟨child, Rows.mem_toRelation.mpr (grown _ member child (Rows.mem_toRelation.mp childMember)), same⟩
    · obtain ⟨child, childMember, same⟩ :=
        participation ⟨p, bound⟩ ⟨j, jBound⟩ row ⟨insert, inDelta, found⟩ inScope
      exact ⟨child, Rows.mem_toRelation.mpr childMember, same⟩
  · -- members are disjoint
    intro subtyping member
    obtain ⟨k, bound, rfl⟩ := List.getElem_of_mem member
    refine List.pairwise_iff_getElem.mpr fun i j iBound jBound before primary first second ↦ ?_
    have oldApart := List.pairwise_iff_getElem.mp (disjoint _ member) i j iBound jBound before
    have differs : (⟨j, jBound⟩ : Fin _) ≠ ⟨i, iBound⟩ := fun same ↦ by
      have := congrArg Fin.val same
      simp only at this
      omega
    rcases ((coherent.member ⟨k, bound⟩ ⟨i, iBound⟩).mem_appended appended primary).mp first with
      firstOld | ⟨insert, inDelta, row, found, rfl⟩
    · rcases ((coherent.member ⟨k, bound⟩ ⟨j, jBound⟩).mem_appended appended _).mp second with
        secondOld | ⟨insert, inDelta, row, found, same⟩
      · exact oldApart _ firstOld secondOld
      · exact (memberOk ⟨k, bound⟩ ⟨j, jBound⟩ row ⟨insert, inDelta, found⟩).2 ⟨i, iBound⟩ differs.symm
          (same ▸ first)
    · exact (memberOk ⟨k, bound⟩ ⟨i, iBound⟩ row ⟨insert, inDelta, found⟩).2 ⟨j, jBound⟩ differs second
  · -- coverage
    intro subtyping member primary inside
    obtain ⟨k, bound, rfl⟩ := List.getElem_of_mem member
    simp only [Subtyping.covered, Relation.mem_project, Relation.mem_select] at inside
    obtain ⟨superRow, ⟨superMember, inScope⟩, rfl⟩ := inside
    rcases ((coherent.supertype ⟨k, bound⟩).mem_appended appended superRow).mp superMember with
      old | ⟨insert, inDelta, row, found, rfl⟩
    · obtain ⟨memberEntry, memberMember, inKeys⟩ := covered _ member _ (by
        simp only [Subtyping.covered, Relation.mem_project, Relation.mem_select]
        exact ⟨_, ⟨old, inScope⟩, rfl⟩)
      obtain ⟨m, mBound, rfl⟩ := List.getElem_of_mem memberMember
      exact ⟨_, memberMember, (coherent.member ⟨k, bound⟩ ⟨m, mBound⟩).mono grown inKeys⟩
    · exact cover ⟨k, bound⟩ row ⟨insert, inDelta, found⟩ inScope

/-- A delta whose appending the full check accepts (no conflict, every table holding exactly its
old rows and the delta's, and a valid result) is accepted. -/
theorem accepts_of_valid [schema.Wiring] [coherent : schema.Coherent] {previous : Snapshot}
    {delta : List (Insert schema)} (none : schema.firstConflict? previous delta = none)
    (appended : schema.Appended previous delta (schema.applied previous delta))
    (valid : schema.Valid (schema.applied previous delta)) : schema.Accepts previous delta := by
  obtain ⟨keys, foreignKeys, typed, participations, disjoint, covered, _⟩ := valid
  refine ⟨keysAgree_of_firstConflict?_eq_none none, ?_, ?_, ?_, ?_, ?_⟩
  · intro q row added uniqueKey uniqueMember other otherMember same
    exact (keys _ (List.getElem_mem q.isLt) uniqueKey uniqueMember).eq_of_key
      (Rows.mem_toRelation.mpr otherMember) (Rows.mem_toRelation.mpr (appended.mem_of_added added)) same
  · intro q row added foreignKey foreignMember
    exact foreignKeys _ (List.getElem_mem q.isLt) foreignKey foreignMember row
      (Rows.mem_toRelation.mpr (appended.mem_of_added added))
  · intro p j row added inScope
    obtain ⟨child, childMember, same⟩ := participations _ (List.getElem_mem p.isLt) _
      (List.getElem_mem j.isLt) _ ((coherent.participation p j).mem_of_added appended added) inScope
    exact ⟨child, Rows.mem_toRelation.mp childMember, same⟩
  · intro k m row added
    have inside := (coherent.member k m).mem_of_added appended added
    refine ⟨typed _ (List.getElem_mem k.isLt) _ (List.getElem_mem m.isLt) _ inside, fun other differs also ↦ ?_⟩
    have pairwise := List.pairwise_iff_getElem.mp (disjoint _ (List.getElem_mem k.isLt))
    rcases Nat.lt_or_gt_of_ne (fun same : other.val = m.val ↦ differs (Fin.ext same)) with before | after
    · exact pairwise other m other.isLt m.isLt before _ also inside
    · exact pairwise m other m.isLt other.isLt after _ inside also
  · intro k row added inScope
    refine covered _ (List.getElem_mem k.isLt) _ ?_
    simp only [Subtyping.covered, Relation.mem_project, Relation.mem_select]
    exact ⟨_, ⟨(coherent.supertype k).mem_of_added appended added, inScope⟩, rfl⟩

/-- **The incremental check is exact.**  On a valid database, a delta is accepted exactly when the
full check accepts appending it: no two different rows share a primary key, every table then holds
exactly its old rows and the delta's, and the result is valid. -/
theorem accepts_iff [schema.Wiring] [schema.Coherent] {previous : Snapshot} {delta : List (Insert schema)}
    (valid : schema.Valid previous) :
    schema.Accepts previous delta ↔
      schema.firstConflict? previous delta = none ∧
        schema.Appended previous delta (schema.applied previous delta) ∧
        schema.Valid (schema.applied previous delta) :=
  ⟨fun accepts ↦ ⟨firstConflict?_eq_none_of_keysAgree accepts.1, appended_of_keysAgree accepts.1,
      valid_of_accepts valid accepts⟩,
    fun ⟨noConflict, appended, valid⟩ ↦ accepts_of_valid noConflict appended valid⟩

/-! #### One row at a time: what a caller proves -/

theorem added_singleton {insert : Insert schema} {q : Fin schema.tables.length} {row : schema.tables[q].Row} :
    Added [insert] q row ↔ insert.rowAt q = some row := by
  simp [Added]

/-- The one row an insert adds, at its own position. -/
theorem added_singleton_self {insert : Insert schema} {q : Fin schema.tables.length}
    {row : schema.tables[q].Row} (added : Added [insert] q row) :
    ∃ same : insert.position = q, cast (congrArg (fun position ↦ schema.tables[position].Row) same)
      insert.row = row :=
  Insert.rowAt_eq_some (added_singleton.mp added)

/-- One row agrees on primary keys with a snapshot where no different row of its table has its
primary key. -/
theorem keysAgree_singleton {previous : Snapshot} {insert : Insert schema}
    (fresh : ∀ old : schema.tables[insert.position].Row, old ∈ schema.tables[insert.position].table.rows previous →
      schema.tables[insert.position].key old = schema.tables[insert.position].key insert.row → old = insert.row) :
    schema.KeysAgree previous [insert] := by
  intro q a b inA inB same
  rcases inA with oldA | addedA <;> rcases inB with oldB | addedB
  · exact Rows.key_injective oldA oldB same
  · obtain ⟨rfl, rfl⟩ := added_singleton_self addedB
    exact fresh a oldA same
  · obtain ⟨rfl, rfl⟩ := added_singleton_self addedA
    exact (fresh b oldB same.symm).symm
  · obtain ⟨rfl, rfl⟩ := added_singleton_self addedA
    obtain ⟨_, rfl⟩ := added_singleton_self addedB
    rfl

/-- One row keeps its table's further unique keys where no other row of the table shares one
with it. -/
theorem uniqueAccepted_singleton [schema.Wiring] {previous : Snapshot} {insert : Insert schema}
    (agree : schema.KeysAgree previous [insert])
    (unique : ∀ key : UniqueKey schema.tables[insert.position].Row,
      key ∈ schema.tables[insert.position].table.uniqueKeys →
      ∀ other : schema.tables[insert.position].Row, other ∈ schema.tables[insert.position].table.rows previous →
        key.key other = key.key insert.row → other = insert.row) :
    UniqueAccepted [insert] (schema.applied previous [insert]) := by
  intro q row added key member other otherMember same
  obtain ⟨rfl, rfl⟩ := added_singleton_self added
  rcases (appended_of_keysAgree agree).old_or_added otherMember with old | otherAdded
  · exact unique key member other old same
  · obtain ⟨_, rfl⟩ := added_singleton_self otherAdded
    rfl

/-- One row keeps its foreign keys where each finds a parent it may refer to in the old
snapshot. -/
theorem foreignAccepted_singleton [schema.Wiring] [coherent : schema.Coherent] {previous : Snapshot}
    {insert : Insert schema} (agree : schema.KeysAgree previous [insert])
    (found : ∀ foreign : ForeignKey Snapshot schema.tables[insert.position].Row,
      foreign ∈ schema.tables[insert.position].table.foreignKeys →
      ∃ parent ∈ foreign.parents previous, foreign.allowed insert.row parent = true ∧
        foreign.primary parent = foreign.reference insert.row) :
    ForeignAccepted [insert] (schema.applied previous [insert]) := by
  intro q row added foreign member
  obtain ⟨rfl, rfl⟩ := added_singleton_self added
  obtain ⟨j, bound, rfl⟩ := List.getElem_of_mem member
  obtain ⟨parent, parentMember, allowed, same⟩ := found _ member
  exact ⟨parent, (coherent.foreignKey insert.position ⟨j, bound⟩).mono (appended_of_keysAgree agree).extends
    parentMember, allowed, same⟩

/-- A row of a table that no mandatory participation reads as its parents breaks none. -/
theorem participationAccepted_of_unread [coherent : schema.Coherent] {next : Snapshot} {insert : Insert schema}
    (unread : ∀ p j, (coherent.participation p j).position ≠ insert.position) :
    ParticipationAccepted [insert] next := fun p j _ added ↦
  absurd (added_singleton_self added).1 (Ne.symm (unread p j))

/-- A row of a table that is no member of a subtyping breaks no member's typing or disjointness. -/
theorem memberAccepted_of_unread [coherent : schema.Coherent] {next : Snapshot} {insert : Insert schema}
    (unread : ∀ k m, (coherent.member k m).position ≠ insert.position) :
    MemberAccepted [insert] next := fun k m _ added ↦
  absurd (added_singleton_self added).1 (Ne.symm (unread k m))

/-- A row of a table that is no supertype of a subtyping breaks no coverage. -/
theorem coverAccepted_of_unread [coherent : schema.Coherent] {next : Snapshot} {insert : Insert schema}
    (unread : ∀ k, (coherent.supertype k).position ≠ insert.position) :
    CoverAccepted [insert] next := fun k _ added ↦
  absurd (added_singleton_self added).1 (Ne.symm (unread k))

/-- One row of a table that no participation or subtyping reads is accepted where its primary key
and further unique keys are its own and its foreign keys find parents in the old snapshot. -/
theorem accepts_singleton [schema.Wiring] [coherent : schema.Coherent] {previous : Snapshot}
    {insert : Insert schema}
    (fresh : ∀ old : schema.tables[insert.position].Row, old ∈ schema.tables[insert.position].table.rows previous →
      schema.tables[insert.position].key old = schema.tables[insert.position].key insert.row → old = insert.row)
    (unique : ∀ key : UniqueKey schema.tables[insert.position].Row,
      key ∈ schema.tables[insert.position].table.uniqueKeys →
      ∀ other : schema.tables[insert.position].Row, other ∈ schema.tables[insert.position].table.rows previous →
        key.key other = key.key insert.row → other = insert.row)
    (found : ∀ foreign : ForeignKey Snapshot schema.tables[insert.position].Row,
      foreign ∈ schema.tables[insert.position].table.foreignKeys →
      ∃ parent ∈ foreign.parents previous, foreign.allowed insert.row parent = true ∧
        foreign.primary parent = foreign.reference insert.row)
    (noParticipation : ∀ p j, (coherent.participation p j).position ≠ insert.position)
    (noMember : ∀ k m, (coherent.member k m).position ≠ insert.position)
    (noSupertype : ∀ k, (coherent.supertype k).position ≠ insert.position) :
    schema.Accepts previous [insert] :=
  have agree := keysAgree_singleton fresh
  ⟨agree, uniqueAccepted_singleton agree unique, foreignAccepted_singleton agree found,
    participationAccepted_of_unread noParticipation, memberAccepted_of_unread noMember,
    coverAccepted_of_unread noSupertype⟩

/-- `table.insert row` is for the table's position in the schema. -/
@[simp] theorem _root_.Relational.Table.insert_position {Row Key : Type} [DecidableEq Row] [TreeOrd Key]
    {key : Row → Key} {table : Table Snapshot key} [entry : InSchema schema table] (row : Row) :
    (table.insert row : Insert schema).position = entry.position :=
  rfl

/-- `accepts_singleton` for `table.insert row`, with its conditions stated through the table itself
rather than through the schema's table at the insert's position, as a caller proves them: the row's
primary key and further unique keys are its own, its foreign keys find parents in the old snapshot,
and no participation or subtyping reads its table.  The last three are about positions alone, so
for a concrete schema `decide` proves them. -/
theorem accepts_insert [schema.Wiring] [coherent : schema.Coherent] {Row Key : Type} [DecidableEq Row]
    [TreeOrd Key] {key : Row → Key} {table : Table Snapshot key} [entry : InSchema schema table]
    {previous : Snapshot} {row : Row}
    (fresh : ∀ old ∈ table.rows previous, key old = key row → old = row)
    (unique : ∀ unique ∈ table.uniqueKeys, ∀ other ∈ table.rows previous,
      unique.key other = unique.key row → other = row)
    (found : ∀ foreign ∈ table.foreignKeys, ∃ parent ∈ foreign.parents previous,
      foreign.allowed row parent = true ∧ foreign.primary parent = foreign.reference row)
    (noParticipation : ∀ p j, (coherent.participation p j).position ≠ entry.position)
    (noMember : ∀ k m, (coherent.member k m).position ≠ entry.position)
    (noSupertype : ∀ k, (coherent.supertype k).position ≠ entry.position) :
    schema.Accepts previous [table.insert row] := by
  -- each condition, for any table equal to `table`, so that the equality `entry.listed` can be
  -- substituted away
  have fresh' : ∀ (t : AnyTable Snapshot) (same : t = table) (old : t.Row), old ∈ t.table.rows previous →
      t.key old = t.key (cast (congrArg AnyTable.Row same).symm row) →
      old = cast (congrArg AnyTable.Row same).symm row := by
    rintro t rfl
    exact fresh
  have unique' : ∀ (t : AnyTable Snapshot) (same : t = table) (u : UniqueKey t.Row), u ∈ t.table.uniqueKeys →
      ∀ other : t.Row, other ∈ t.table.rows previous →
      u.key other = u.key (cast (congrArg AnyTable.Row same).symm row) →
      other = cast (congrArg AnyTable.Row same).symm row := by
    rintro t rfl
    exact unique
  have found' : ∀ (t : AnyTable Snapshot) (same : t = table) (foreign : ForeignKey Snapshot t.Row),
      foreign ∈ t.table.foreignKeys → ∃ parent ∈ foreign.parents previous,
        foreign.allowed (cast (congrArg AnyTable.Row same).symm row) parent = true ∧
        foreign.primary parent = foreign.reference (cast (congrArg AnyTable.Row same).symm row) := by
    rintro t rfl
    exact found
  exact accepts_singleton (insert := table.insert row) (fresh' _ entry.listed) (unique' _ entry.listed)
    (found' _ entry.listed) noParticipation noMember noSupertype

end Schema

end Relational
