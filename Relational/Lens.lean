module

public import Relational.Database

-- The families' bodies are unfolded by the bridge lemmas that `schema_laws%` proves by `rfl` in the
-- modules of the schemas.
@[expose] public section -- principles: ignore[lean:expose-section] schema_laws% unfolds the families by rfl

namespace Relational

/-! The laws of a schema's readers and writers, proved once here and wired to a schema by
`schema_laws%` (Relational/SchemaLaws.lean).  A snapshot is read and written through a family of
lenses, one per table and per index (`Family`), whose laws (`Family.Lawful`) say that reading a
part after writing it gives what was written, and that writing one part leaves every other part
alone.  A schema's family is composed of a family over the snapshot's fields and, for each field,
one over the tables of the group it holds (`Family.compose`), or the field itself (`Family.single`),
so that `schema_laws%` proves each family's laws by cases over a few fields, not over every pair of
tables.  `Wired` says that the tables of a schema, with their indexes, are distinct parts of such a
family, and `Wired.wiring` turns that into `Schema.Wiring`: the laws over positions in the schema's
tables, as the theorems about appending need them. -/

/-- A family of lenses into `S`: for each `i`, a part of type `Slot i` that `get` reads and `set`
replaces. -/
structure Family (S : Type) (ι : Type) (Slot : ι → Type) where
  get : S → (i : ι) → Slot i
  set : S → (i : ι) → Slot i → S

namespace Family

variable {S ι : Type} {Slot : ι → Type}

/-- Reading a part after writing it gives what was written, and writing a part leaves every other
part as it was. -/
structure Lawful (F : Family S ι Slot) : Prop where
  get_set : ∀ s i v, F.get (F.set s i v) i = v
  get_set_ne : ∀ s i j v, i ≠ j → F.get (F.set s i v) j = F.get s j

/-- The whole of `T` as its one part. -/
def single (T : Type) : Family T Unit (fun _ ↦ T) where
  get s _ := s
  set _ _ v := v

theorem single_lawful (T : Type) : (single T).Lawful where
  get_set _ _ _ := rfl
  get_set_ne _ i j _ ne := (ne (by cases i; cases j; rfl)).elim

/-- Parts addressed by a part `a` of the outer family `O` and a part of it in the family `I a`. -/
def compose {γ : Type} {Outer : γ → Type} {Idx : γ → Type} {Slot : (Σ a, Idx a) → Type}
    (O : Family S γ Outer) (I : (a : γ) → Family (Outer a) (Idx a) (fun k ↦ Slot ⟨a, k⟩)) :
    Family S (Σ a, Idx a) Slot where
  get s i := (I i.1).get (O.get s i.1) i.2
  set s i v := O.set s i.1 ((I i.1).set (O.get s i.1) i.2 v)

theorem compose_lawful {γ : Type} {Outer : γ → Type} {Idx : γ → Type}
    {Slot : (Σ a, Idx a) → Type}
    (O : Family S γ Outer) (I : (a : γ) → Family (Outer a) (Idx a) (fun k ↦ Slot ⟨a, k⟩))
    (outer : O.Lawful) (inner : ∀ a, (I a).Lawful) : (compose O I).Lawful where
  get_set s i v := by
    obtain ⟨a, k⟩ := i
    simp only [compose, outer.get_set, (inner a).get_set]
  get_set_ne s i j v ne := by
    obtain ⟨a, k⟩ := i
    obtain ⟨b, l⟩ := j
    simp only [compose]
    by_cases same : a = b
    · subst same
      have different : k ≠ l := fun equal ↦ ne (equal ▸ rfl)
      rw [outer.get_set, (inner a).get_set_ne _ _ _ _ different]
    · rw [outer.get_set_ne _ _ _ _ same]

end Family

variable {S ι : Type} {Slot : ι → Type}

/-- The indexes `indexes` of the table at position `k`, from the `j`th on, are parts of `F`: each
read and replaced as its part, which `rank` numbers `(k, j + 1)` for the `j`th, so that no two
indexes, and no index and table, are the same part. -/
inductive IndexesWired (F : Family S ι Slot) (rank : ι → Nat × Nat) (k : Nat) {Row Key : Type}
    [TreeOrd Key] {key : Row → Key} : Nat → List (TableIndex S key) → Prop
  | nil (j : Nat) : IndexesWired F rank k j []
  | cons (j : Nat) (index : TableIndex S key) (i : ι) (rest : List (TableIndex S key))
      (slot : Slot i = Index key index.column) (ranked : rank i = (k, j + 1))
      (get_eq : ∀ s, index.get s = cast slot (F.get s i))
      (set_eq : ∀ s v, index.set s v = F.set s i (cast slot.symm v))
      (tail : IndexesWired F rank k (j + 1) rest) : IndexesWired F rank k j (index :: rest)

/-- The tables `entries`, from position `k` on, and their indexes are parts of `F`: each table read
and replaced as its part, which `rank` numbers `(k, 0)` for the table at position `k`. -/
inductive Wired (F : Family S ι Slot) (rank : ι → Nat × Nat) : Nat → List (AnyTable S) → Prop
  | nil (k : Nat) : Wired F rank k []
  | cons (k : Nat) (entry : AnyTable S) (i : ι) (rest : List (AnyTable S))
      (slot : Slot i = Rows entry.key) (ranked : rank i = (k, 0))
      (rows_eq : ∀ s, entry.table.rows s = cast slot (F.get s i))
      (set_eq : ∀ s r, entry.table.set s r = F.set s i (cast slot.symm r))
      (indexes : IndexesWired F rank k 0 entry.table.indexes)
      (tail : Wired F rank (k + 1) rest) : Wired F rank k (entry :: rest)

/-- The part of the index at position `p` of a wired list of indexes. -/
theorem IndexesWired.get {F : Family S ι Slot} {rank : ι → Nat × Nat} {k : Nat} {Row Key : Type}
    [TreeOrd Key] {key : Row → Key} :
    ∀ {j : Nat} {indexes : List (TableIndex S key)}, IndexesWired F rank k j indexes →
      ∀ (p : Nat) (bound : p < indexes.length), ∃ i, ∃ slot : Slot i = Index key indexes[p].column,
        rank i = (k, j + p + 1) ∧ (∀ s, indexes[p].get s = cast slot (F.get s i)) ∧
        (∀ s v, indexes[p].set s v = F.set s i (cast slot.symm v))
  | _, _, .nil _, _, bound => absurd bound (Nat.not_lt_zero _)
  | _, _, .cons _ _ i _ slot ranked get_eq set_eq _, 0, _ => ⟨i, slot, ranked, get_eq, set_eq⟩
  | _, _, .cons j _ _ _ _ _ _ _ tail, p + 1, bound => by
    obtain ⟨i, slot, ranked, get_eq, set_eq⟩ := tail.get p (Nat.lt_of_succ_lt_succ bound)
    refine ⟨i, slot, ?_, get_eq, set_eq⟩
    rw [ranked]
    congr 1
    omega

/-- The part of the table at position `p` of a wired list of tables, and its indexes. -/
theorem Wired.get {F : Family S ι Slot} {rank : ι → Nat × Nat} :
    ∀ {k : Nat} {entries : List (AnyTable S)}, Wired F rank k entries →
      ∀ (p : Nat) (bound : p < entries.length), ∃ i, ∃ slot : Slot i = Rows entries[p].key,
        rank i = (k + p, 0) ∧ (∀ s, entries[p].table.rows s = cast slot (F.get s i)) ∧
        (∀ s r, entries[p].table.set s r = F.set s i (cast slot.symm r)) ∧
        IndexesWired F rank (k + p) 0 entries[p].table.indexes
  | _, _, .nil _, _, bound => absurd bound (Nat.not_lt_zero _)
  | _, _, .cons _ _ i _ slot ranked rows_eq set_eq indexes _, 0, _ =>
    ⟨i, slot, ranked, rows_eq, set_eq, indexes⟩
  | _, _, .cons k _ _ _ _ _ _ _ _ tail, p + 1, bound => by
    obtain ⟨i, slot, ranked, rows_eq, set_eq, indexes⟩ := tail.get p (Nat.lt_of_succ_lt_succ bound)
    have same : k + 1 + p = k + (p + 1) := by omega
    rw [same] at ranked indexes
    exact ⟨i, slot, ranked, rows_eq, set_eq, indexes⟩

/-- The `j`th index of the table at position `p` of `schema`. -/
abbrev Schema.indexAt {Snapshot : Type} (schema : Schema Snapshot) (p : Fin schema.tables.length)
    (j : Fin schema.tables[p].table.indexes.length) : TableIndex Snapshot schema.tables[p].key :=
  schema.tables[p].table.indexes[j]

/-- The laws of a schema's readers and writers, over positions in its tables: a table reads back
the rows written to it and an index what was written to it, and writing a table or an index leaves
every other table and index as it was.  `schema_laws%` proves them for a schema
(`Wired.wiring`). -/
class Schema.Wiring {Snapshot : Type} (schema : Schema Snapshot) : Prop where
  rows_set : ∀ (p : Fin schema.tables.length) (s : Snapshot) (r : Rows schema.tables[p].key),
    schema.tables[p].table.rows (schema.tables[p].table.set s r) = r
  rows_set_ne : ∀ (p q : Fin schema.tables.length), p ≠ q →
    ∀ (s : Snapshot) (r : Rows schema.tables[p].key),
      schema.tables[q].table.rows (schema.tables[p].table.set s r) = schema.tables[q].table.rows s
  index_get_set : ∀ (p : Fin schema.tables.length) (j : Fin schema.tables[p].table.indexes.length)
    (s : Snapshot) (v : Index schema.tables[p].key (schema.indexAt p j).column),
      (schema.indexAt p j).get ((schema.indexAt p j).set s v) = v
  index_get_set_ne : ∀ (p : Fin schema.tables.length) (j : Fin schema.tables[p].table.indexes.length)
    (q : Fin schema.tables.length) (l : Fin schema.tables[q].table.indexes.length),
    p ≠ q ∨ j.val ≠ l.val →
    ∀ (s : Snapshot) (v : Index schema.tables[p].key (schema.indexAt p j).column),
      (schema.indexAt q l).get ((schema.indexAt p j).set s v) = (schema.indexAt q l).get s
  rows_index_set : ∀ (p : Fin schema.tables.length) (j : Fin schema.tables[p].table.indexes.length)
    (q : Fin schema.tables.length) (s : Snapshot)
    (v : Index schema.tables[p].key (schema.indexAt p j).column),
      schema.tables[q].table.rows ((schema.indexAt p j).set s v) = schema.tables[q].table.rows s
  index_get_rows_set : ∀ (p q : Fin schema.tables.length)
    (l : Fin schema.tables[q].table.indexes.length) (s : Snapshot) (r : Rows schema.tables[p].key),
      (schema.indexAt q l).get (schema.tables[p].table.set s r) = (schema.indexAt q l).get s

/-- A schema whose tables and indexes are distinct parts of a lawful family satisfies the laws. -/
theorem Wired.wiring {Snapshot : Type} {schema : Schema Snapshot} {Slot : ι → Type}
    {F : Family Snapshot ι Slot} {rank : ι → Nat × Nat} (lawful : F.Lawful)
    (wired : Wired F rank 0 schema.tables) : schema.Wiring := by
  -- the parts of two tables, two indexes or a table and an index at different positions differ
  have apart {i i' : ι} {x y : Nat × Nat} (ranked : rank i = x) (ranked' : rank i' = y)
      (different : x ≠ y) : i ≠ i' := fun same ↦ different (ranked ▸ ranked' ▸ congrArg rank same)
  have table (p : Fin schema.tables.length) := wired.get p.val p.isLt
  have index (p : Fin schema.tables.length) (j : Fin schema.tables[p].table.indexes.length) :
      ∃ i, ∃ slot : Slot i = Index schema.tables[p].key (schema.indexAt p j).column,
        rank i = (0 + p.val, 0 + j.val + 1) ∧
        (∀ s, (schema.indexAt p j).get s = cast slot (F.get s i)) ∧
        (∀ s v, (schema.indexAt p j).set s v = F.set s i (cast slot.symm v)) := by
    obtain ⟨_, _, _, _, _, indexes⟩ := table p
    exact indexes.get j.val j.isLt
  constructor
  · intro p s r
    obtain ⟨i, slot, _, rows_eq, set_eq, _⟩ := table p
    simp only [Fin.getElem_fin] at *
    rw [set_eq, rows_eq, lawful.get_set, cast_cast, cast_eq]
  · intro p q different s r
    obtain ⟨i, slot, ranked, _, set_eq, _⟩ := table p
    obtain ⟨i', slot', ranked', rows_eq', _, _⟩ := table q
    have ne : i ≠ i' := apart ranked ranked' fun same ↦
      different (Fin.ext (by simpa using congrArg Prod.fst same))
    simp only [Fin.getElem_fin] at *
    rw [set_eq, rows_eq', lawful.get_set_ne _ _ _ _ ne, ← rows_eq']
  · intro p j s v
    obtain ⟨i, slot, _, get_eq, set_eq⟩ := index p j
    simp only [Fin.getElem_fin] at *
    rw [set_eq, get_eq, lawful.get_set, cast_cast, cast_eq]
  · intro p j q l different s v
    obtain ⟨i, slot, ranked, _, set_eq⟩ := index p j
    obtain ⟨i', slot', ranked', get_eq', _⟩ := index q l
    have ne : i ≠ i' := apart ranked ranked' fun same ↦ by
      simp only [Nat.zero_add, Prod.mk.injEq, Nat.add_right_cancel_iff] at same
      rcases different with different | different
      · exact different (Fin.ext same.1)
      · exact different same.2
    simp only [Fin.getElem_fin] at *
    rw [set_eq, get_eq', lawful.get_set_ne _ _ _ _ ne, ← get_eq']
  · intro p j q s v
    obtain ⟨i, slot, ranked, _, set_eq⟩ := index p j
    obtain ⟨i', slot', ranked', rows_eq', _, _⟩ := table q
    have ne : i ≠ i' := apart ranked ranked' fun same ↦ by
      simp only [Nat.zero_add, Prod.mk.injEq] at same
      exact Nat.succ_ne_zero _ same.2
    simp only [Fin.getElem_fin] at *
    rw [set_eq, rows_eq', lawful.get_set_ne _ _ _ _ ne, ← rows_eq']
  · intro p q l s r
    obtain ⟨i, slot, ranked, _, set_eq, _⟩ := table p
    obtain ⟨i', slot', ranked', get_eq', _⟩ := index q l
    have ne : i ≠ i' := apart ranked ranked' fun same ↦ by
      simp only [Nat.zero_add, Prod.mk.injEq] at same
      exact Nat.succ_ne_zero _ same.2.symm
    simp only [Fin.getElem_fin] at *
    rw [set_eq, get_eq', lawful.get_set_ne _ _ _ _ ne, ← get_eq']

end Relational
