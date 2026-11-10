module

public import Std.Data.ExtTreeMap
public import Std.Data.ExtTreeSet
public import Relational.ListKeys
public import Relational.TreeOrd
public import DeriveMapM
-- the `#guard`s at the end run code from this import
meta import DeriveMapM


public section

namespace Relational

/-! Finite typed relations with bag semantics.  A `Relation Row` is a quotient of lists by
permutation, so no function of a relation can observe the order of the rows in the list behind it:
Lean accepts a function out of the quotient only together with a proof that permuted lists give the
same result.  Repetition is kept, as in SQL without `DISTINCT`: `project` keeps every image and
`union` is the sum of the two bags, so that a sum over a projection counts every row (`reduce`).
That a relation repeats no row is a key like any other, the identity (`Keyed id`), which `distinct`
establishes and every table's relation has (`Rows.toRelation_keyed`).  Order that matters is data,
a column read by `minBy`, `maxBy`, `maxByGroup` and `sortedBy?`; there is no `toList`.  Every
query has a law stated by membership, and `count`, `union` and `reduce` laws stated by how often
rows occur (`multiplicity`); relations are equal exactly when every row occurs in them equally often
(`Relation.eq_iff_multiplicity`), and two relations without repeated rows when they have the same
members (`Relation.ext`).  Each operation states its cost in the lengths n and m of the lists behind
its arguments.  Joins on a key and `sortedBy?` go through balanced trees, and so does `distinct`
where the rows have a lawful order, in O(n log n) time for n rows in all; `join`, `semijoin` and
`antijoin` with an arbitrary predicate compare every pair. -/

/-- Two lists have the same members, whatever their order and repetition. -/
@[expose] def SameMembers {Row : Type} (left right : List Row) : Prop := ∀ row, row ∈ left ↔ row ∈ right

/-- Permuted lists have the same members. -/
theorem _root_.List.Perm.sameMembers {Row : Type} {left right : List Row} (same : left.Perm right) :
    SameMembers left right := fun _ ↦ same.mem_iff

/-- A finite bag of rows: a list up to the order of its entries. -/
@[expose] def Relation (Row : Type) : Type := Quotient (List.isSetoid Row)

/-- A commutative monoid, with its laws: what a relation can be reduced with whatever the order of
the list behind it, such as a sum, a count, a maximum with a least element, or a union. -/
structure CommMonoid (M : Type) where
  unit : M
  op : M → M → M
  assoc : ∀ first second third, op (op first second) third = op first (op second third)
  comm : ∀ first second, op first second = op second first
  unit_op : ∀ value, op unit value = value

namespace CommMonoid

variable {M : Type} (monoid : CommMonoid M)

/-- Addition of natural numbers, for counts and sums. -/
def nat : CommMonoid Nat := ⟨0, (· + ·), Nat.add_assoc, Nat.add_comm, Nat.zero_add⟩

/-- The maximum of natural numbers, 0 the least, for the greatest count or place. -/
def max : CommMonoid Nat := ⟨0, Max.max, Nat.max_assoc, Nat.max_comm, Nat.zero_max⟩

theorem op_unit (value : M) : monoid.op value monoid.unit = value := by
  rw [monoid.comm, monoid.unit_op]

private theorem foldr_append (left right : List M) :
    (left ++ right).foldr monoid.op monoid.unit =
      monoid.op (left.foldr monoid.op monoid.unit) (right.foldr monoid.op monoid.unit) := by
  induction left with
  | nil => simp [monoid.unit_op]
  | cons head rest ih => simp [ih, monoid.assoc]

/-- Combines neighbours: the first value with the second, the third with the fourth, and so on. -/
private def pairUp : List M → List M
  | first :: second :: rest => monoid.op first second :: pairUp rest
  | values => values

private theorem length_pairUp : ∀ (first second : M) (rest : List M),
    (monoid.pairUp (first :: second :: rest)).length < (first :: second :: rest).length
  | _, _, [] => by simp [pairUp]
  | _, _, [_] => by simp [pairUp]
  | _, _, third :: fourth :: rest => by
    have := length_pairUp third fourth rest
    simp only [pairUp, List.length_cons] at this ⊢
    omega

/-- Combines `values` in a balanced tree of `op`, built level by level from neighbours: n - 1
applications of `op`, O(n) work in all and O(log n) levels.  The balance pays where `op` costs
more on bigger values, as merging sorted lists or trees does; a later version may combine the
halves of a level in parallel. -/
def combine : List M → M
  | [] => monoid.unit
  | [value] => value
  | first :: second :: rest => combine (monoid.pairUp (first :: second :: rest))
termination_by values => values.length
decreasing_by exact monoid.length_pairUp first second rest

private theorem foldr_pairUp : ∀ values : List M,
    (monoid.pairUp values).foldr monoid.op monoid.unit = values.foldr monoid.op monoid.unit
  | first :: second :: rest => by
    simp only [pairUp, List.foldr_cons, foldr_pairUp rest, monoid.assoc]
  | [] | [_] => rfl

/-- Pairing changes only the shape of the tree: by associativity it is the fold. -/
theorem combine_eq_foldr : ∀ values : List M, monoid.combine values = values.foldr monoid.op monoid.unit
  | [] => by rw [combine]; rfl
  | [value] => by rw [combine]; simp [monoid.op_unit]
  | first :: second :: rest => by
    rw [combine, combine_eq_foldr, foldr_pairUp]
termination_by values => values.length
decreasing_by exact monoid.length_pairUp first second rest

/-- A commutative monoid's fold does not see the order of the list. -/
theorem foldr_perm {left right : List M} (same : left.Perm right) :
    left.foldr monoid.op monoid.unit = right.foldr monoid.op monoid.unit :=
  same.foldr_eq' (fun first _ second _ third ↦ by
    rw [← monoid.assoc, ← monoid.assoc, monoid.comm second first]) _

end CommMonoid

namespace Relation

variable {Row Left Right Result Key : Type}

/-- The relation whose members are the elements of `rows`, behind which the list stays as it is,
repetitions included. -/
@[expose] def ofList (rows : List Row) : Relation Row := Quotient.mk _ rows

instance : EmptyCollection (Relation Row) := ⟨ofList []⟩

instance : Membership Row (Relation Row) where
  mem relation row :=
    Quotient.liftOn relation (fun rows ↦ row ∈ rows) fun _ _ same ↦ propext same.mem_iff

@[simp] theorem mem_ofList {rows : List Row} {row : Row} : row ∈ ofList rows ↔ row ∈ rows :=
  Iff.rfl

@[simp] theorem not_mem_empty {row : Row} : row ∉ (∅ : Relation Row) := by
  simp [EmptyCollection.emptyCollection]

/-- Relations whose lists are permutations of each other are equal. -/
theorem sound {left right : List Row} (same : left.Perm right) : ofList left = ofList right :=
  Quotient.sound same

theorem ofList_eq_ofList {left right : List Row} : ofList left = ofList right ↔ left.Perm right :=
  ⟨Quotient.exact, sound⟩

/-- Proves a statement about every relation from the lists behind it. -/
@[elab_as_elim] theorem inductionOn {motive : Relation Row → Prop} (relation : Relation Row)
    (ofList : ∀ rows, motive (ofList rows)) : motive relation :=
  Quotient.inductionOn relation ofList

instance [DecidableEq Row] (row : Row) (relation : Relation Row) : Decidable (row ∈ relation) :=
  Quotient.recOnSubsingleton relation fun rows ↦ inferInstanceAs (Decidable (row ∈ rows))

/-- Lifts a list function that takes permuted lists to permuted lists. -/
private def lift1 {Other : Type} (function : List Row → List Other)
    (respects : ∀ rows other : List Row, rows.Perm other → (function rows).Perm (function other))
    (relation : Relation Row) : Relation Other :=
  Quotient.liftOn relation (fun rows ↦ ofList (function rows)) fun _ _ same ↦
    Quotient.sound (respects _ _ same)

/-- Lifts a binary list function that takes permuted lists to permuted lists. -/
def lift2 {Other : Type} (function : List Left → List Right → List Other)
    (respects : ∀ (left left' : List Left) (right right' : List Right), left.Perm left' →
      right.Perm right' → (function left right).Perm (function left' right'))
    (left : Relation Left) (right : Relation Right) : Relation Other :=
  Quotient.liftOn₂ left right (fun left right ↦ ofList (function left right))
    fun _ _ _ _ sameLeft sameRight ↦ Quotient.sound (respects _ _ _ _ sameLeft sameRight)

/-- Filters of permuted lists by predicates that agree on their members are permuted. -/
private theorem perm_filter {first second : Row → Bool} {left right : List Row}
    (same : left.Perm right) (agree : ∀ row ∈ left, first row = second row) :
    (left.filter first).Perm (right.filter second) := by
  rw [List.filter_congr agree]
  exact same.filter second

/-- `flatMap` of functions that give permuted lists for every member gives permuted lists. -/
private theorem perm_flatMap {first second : Row → List Result} :
    ∀ {rows : List Row}, (∀ row ∈ rows, (first row).Perm (second row)) →
      (rows.flatMap first).Perm (rows.flatMap second)
  | [], _ => List.Perm.refl _
  | row :: rest, same => by
    simp only [List.flatMap_cons]
    exact (same row List.mem_cons_self).append
      (perm_flatMap fun other member ↦ same other (List.mem_cons_of_mem _ member))

/-- The keys of the rows of `rows`. -/
def keySet [TreeOrd Key] (key : Row → Key) (rows : List Row) :
    Std.ExtTreeSet Key TreeOrd.cmp :=
  rows.foldr (fun row keys ↦ keys.insert (key row)) ∅

private theorem mem_keySet [TreeOrd Key] {key : Row → Key}
    {rows : List Row} {value : Key} : value ∈ keySet key rows ↔ ∃ row ∈ rows, key row = value := by
  induction rows with
  | nil => simp [keySet]
  | cons head rest ih =>
    simp only [keySet, List.foldr_cons] at ih ⊢
    rw [Std.ExtTreeSet.mem_insert, ih]
    constructor
    · rintro (same | ⟨row, member, same⟩)
      · exact ⟨head, List.mem_cons_self, Std.LawfulEqCmp.eq_of_compare same⟩
      · exact ⟨row, List.mem_cons_of_mem _ member, same⟩
    · rintro ⟨row, member, same⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact Or.inl (same ▸ Std.ReflCmp.compare_self)
      · exact Or.inr ⟨row, later, same⟩

/-- The rows that satisfy `predicate`, in O(n) time. -/
def select (predicate : Row → Bool) : Relation Row → Relation Row :=
  lift1 (List.filter predicate) fun _ _ same ↦ same.filter predicate

/-- The image of every row under `projection`, in O(n) time, every repetition kept: rows with the
same image give it once each, as SQL's `SELECT` without `DISTINCT` does. -/
def project (projection : Row → Result) : Relation Row → Relation Result :=
  lift1 (List.map projection) fun _ _ same ↦ same.map projection

/-- Pairs of a left and a right row that satisfy `predicate`, by testing every pair: O(n m).  The
result's list repeats a pair only where an argument's list repeats a row. -/
def join (predicate : Left → Right → Bool) :
    Relation Left → Relation Right → Relation (Left × Right) :=
  lift2 (fun left right ↦ left.flatMap fun leftRow ↦
      (right.filter (predicate leftRow)).map (leftRow, ·))
    fun _ _ _ _ sameLeft sameRight ↦ (sameLeft.flatMap_right _).trans
      (perm_flatMap fun _ _ ↦ (sameRight.filter _).map _)

/-- The left rows that some right row matches, by testing every pair: O(n m). -/
def semijoin (predicate : Left → Right → Bool) : Relation Left → Relation Right → Relation Left :=
  lift2 (fun left right ↦ left.filter fun leftRow ↦ right.any (predicate leftRow))
    fun _ _ _ _ sameLeft sameRight ↦ perm_filter sameLeft fun _ _ ↦
      Bool.eq_iff_iff.mpr (by simp [sameRight.mem_iff])

/-- The left rows that no right row matches, by testing every pair: O(n m). -/
def antijoin (predicate : Left → Right → Bool) : Relation Left → Relation Right → Relation Left :=
  lift2 (fun left right ↦ left.filter fun leftRow ↦ !right.any (predicate leftRow))
    fun _ _ _ _ sameLeft sameRight ↦ perm_filter sameLeft fun _ _ ↦
      Bool.eq_iff_iff.mpr (by simp [sameRight.mem_iff])

/-- The rows of both relations, each as often as in the one and the other together (SQL's
`UNION ALL`), in O(n) time; `distinct` after it gives the union of sets.  It is not idempotent: a
relation united with itself has every row twice, so a closure is computed until no new row is
added, never until the union stops changing. -/
def union : Relation Row → Relation Row → Relation Row :=
  lift2 (· ++ ·) fun _ _ _ _ sameLeft sameRight ↦ sameLeft.append sameRight

instance : Union (Relation Row) := ⟨union⟩

/-- The union of the relations of two lists is the relation of the lists appended. -/
theorem union_ofList (left right : List Row) : ofList left ∪ ofList right = ofList (left ++ right) := by
  rfl

/-- Whether some row satisfies `predicate`, in O(n) time. -/
def any (predicate : Row → Bool) (relation : Relation Row) : Bool :=
  Quotient.liftOn relation (·.any predicate) fun left right same ↦ by
    apply Bool.eq_iff_iff.mpr
    simp [same.mem_iff]

/-- Whether every row satisfies `predicate`, in O(n) time. -/
def all (predicate : Row → Bool) (relation : Relation Row) : Bool :=
  Quotient.liftOn relation (·.all predicate) fun left right same ↦ by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact forall_congr' fun row ↦ imp_congr_left same.mem_iff

/-- Whether the relation has no rows, by looking at the first entry of the list. -/
def isEmpty (relation : Relation Row) : Bool := relation.all fun _ ↦ false

/-- The rows of a list that satisfy `predicate`, as a relation. -/
theorem select_ofList (predicate : Row → Bool) (rows : List Row) :
    select predicate (ofList rows) = ofList (rows.filter predicate) := by rfl

@[simp] theorem mem_select {predicate : Row → Bool} {relation : Relation Row} {row : Row} :
    row ∈ select predicate relation ↔ row ∈ relation ∧ predicate row = true := by
  induction relation using inductionOn with
  | ofList rows =>
    show row ∈ rows.filter predicate ↔ row ∈ rows ∧ _
    simp

@[simp] theorem mem_project {projection : Row → Result} {relation : Relation Row}
    {result : Result} :
    result ∈ project projection relation ↔ ∃ row ∈ relation, projection row = result := by
  induction relation using inductionOn with
  | ofList rows =>
    show result ∈ rows.map projection ↔ ∃ row, row ∈ rows ∧ _
    simp

/-- Projecting twice is projecting once, by the composite. -/
@[simp] theorem project_project {Middle : Type} {first : Row → Middle} {second : Middle → Result}
    {relation : Relation Row} :
    project second (project first relation) = project (fun row ↦ second (first row)) relation := by
  induction relation using inductionOn with
  | ofList rows => exact congrArg ofList (List.map_map ..)

/-- A projection that keeps every row as it is keeps the relation. -/
theorem project_id' {projection : Row → Row} (same : ∀ row, projection row = row)
    {relation : Relation Row} : project projection relation = relation := by
  induction relation using inductionOn with
  | ofList rows =>
    show ofList (rows.map projection) = ofList rows
    rw [List.map_congr_left fun row _ ↦ same row, List.map_id']

@[simp] theorem mem_join {predicate : Left → Right → Bool} {left : Relation Left}
    {right : Relation Right} {leftRow : Left} {rightRow : Right} :
    (leftRow, rightRow) ∈ join predicate left right ↔
      leftRow ∈ left ∧ rightRow ∈ right ∧ predicate leftRow rightRow = true := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right =>
    show (leftRow, rightRow) ∈ left.flatMap (fun leftRow ↦
      (right.filter (predicate leftRow)).map (leftRow, ·)) ↔ leftRow ∈ left ∧ rightRow ∈ right ∧ _
    simp

@[simp] theorem mem_semijoin {predicate : Left → Right → Bool} {left : Relation Left}
    {right : Relation Right} {leftRow : Left} :
    leftRow ∈ semijoin predicate left right ↔
      leftRow ∈ left ∧ ∃ rightRow ∈ right, predicate leftRow rightRow = true := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right =>
    show leftRow ∈ left.filter (fun leftRow ↦ right.any (predicate leftRow)) ↔
      leftRow ∈ left ∧ ∃ rightRow, rightRow ∈ right ∧ _
    simp

@[simp] theorem mem_antijoin {predicate : Left → Right → Bool} {left : Relation Left}
    {right : Relation Right} {leftRow : Left} :
    leftRow ∈ antijoin predicate left right ↔
      leftRow ∈ left ∧ ∀ rightRow ∈ right, predicate leftRow rightRow = false := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right =>
    show leftRow ∈ left.filter (fun leftRow ↦ !right.any (predicate leftRow)) ↔
      leftRow ∈ left ∧ ∀ rightRow, rightRow ∈ right → _
    simp

@[simp] theorem mem_union {left right : Relation Row} {row : Row} :
    row ∈ left ∪ right ↔ row ∈ left ∨ row ∈ right := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right =>
    show row ∈ left ++ right ↔ row ∈ left ∨ row ∈ right
    simp

@[simp] theorem any_iff {predicate : Row → Bool} {relation : Relation Row} :
    relation.any predicate = true ↔ ∃ row ∈ relation, predicate row = true := by
  induction relation using inductionOn with
  | ofList rows =>
    show rows.any predicate = true ↔ ∃ row, row ∈ rows ∧ _
    simp

@[simp] theorem all_iff {predicate : Row → Bool} {relation : Relation Row} :
    relation.all predicate = true ↔ ∀ row ∈ relation, predicate row = true := by
  induction relation using inductionOn with
  | ofList rows =>
    show rows.all predicate = true ↔ ∀ row, row ∈ rows → _
    simp

@[simp] theorem isEmpty_iff {relation : Relation Row} :
    relation.isEmpty = true ↔ ∀ row, row ∉ relation := by
  simp [isEmpty]

/-! ### Joins on a key, through a tree

`joinOn`, `semijoinOn` and `antijoinOn` match rows whose keys are equal.  They collect the right
rows by key in a balanced tree and look every left row up in it, in O((n + m) log m) time for n
left and m right rows, plus the size of the result. -/

/-- The rows of `rows` with each value of `key`. -/
private def grouped [TreeOrd Key] (key : Row → Key) (rows : List Row) :
    Std.ExtTreeMap Key (List Row) TreeOrd.cmp :=
  rows.foldr (fun row groups ↦ groups.insert (key row) (row :: groups.getD (key row) [])) ∅

/-- A group is the rows with its key, in the order of the list. -/
private theorem getD_grouped [TreeOrd Key] {key : Row → Key}
    {value : Key} : ∀ {rows : List Row},
      (grouped key rows).getD value [] = rows.filter fun row ↦ TreeOrd.cmp (key row) value == .eq
  | [] => by simp [grouped]
  | head :: rest => by
    have previous := getD_grouped (key := key) (value := value) (rows := rest)
    simp only [grouped, List.foldr_cons] at previous ⊢
    rw [Std.ExtTreeMap.getD_insert, List.filter_cons]
    split
    · rename_i same
      have same' := Std.LawfulEqCmp.eq_of_compare same
      subst same'
      simp [Std.ReflCmp.compare_self, previous]
    · rename_i differs
      simp [differs, previous]

private theorem mem_grouped [TreeOrd Key] {key : Row → Key}
    {rows : List Row} {value : Key} {row : Row} :
    row ∈ (grouped key rows).getD value [] ↔ row ∈ rows ∧ key row = value := by
  rw [getD_grouped, List.mem_filter, beq_iff_eq]
  exact and_congr_right fun _ ↦
    ⟨Std.LawfulEqCmp.eq_of_compare, fun same ↦ same ▸ Std.ReflCmp.compare_self⟩

/-- Pairs of a left and a right row, matched through a tree of the right rows by key. -/
private def joinRows [TreeOrd Key] (leftKey : Left → Key) (rightKey : Right → Key)
    (left : List Left) (right : List Right) : List (Left × Right) :=
  let groups := grouped rightKey right
  left.flatMap fun leftRow ↦ (groups.getD (leftKey leftRow) []).map (leftRow, ·)

private theorem mem_joinRows [TreeOrd Key]
    {leftKey : Left → Key} {rightKey : Right → Key} {left : List Left} {right : List Right}
    {leftRow : Left} {rightRow : Right} :
    (leftRow, rightRow) ∈ joinRows leftKey rightKey left right ↔
      leftRow ∈ left ∧ rightRow ∈ right ∧ leftKey leftRow = rightKey rightRow := by
  simp only [joinRows, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨other, member, row, found, rfl, rfl⟩
    obtain ⟨rightMember, same⟩ := mem_grouped.mp found
    exact ⟨member, rightMember, same.symm⟩
  · rintro ⟨member, rightMember, same⟩
    exact ⟨leftRow, member, rightRow, mem_grouped.mpr ⟨rightMember, same.symm⟩, rfl, rfl⟩

/-- Pairs of a left and a right row with equal keys, in O((n + m) log m) time plus the length of
the result, whose list repeats a pair only where an argument's list repeats a row.  Key domains
must coincide; this does not assert uniqueness or referential integrity. -/
def joinOn [TreeOrd Key] (leftKey : Left → Key)
    (rightKey : Right → Key) : Relation Left → Relation Right → Relation (Left × Right) :=
  lift2 (joinRows leftKey rightKey) fun _ _ _ _ sameLeft sameRight ↦ by
    simp only [joinRows, getD_grouped]
    exact (sameLeft.flatMap_right _).trans (perm_flatMap fun _ _ ↦ (sameRight.filter _).map _)

/-- The left rows whose key some right row has, in O((n + m) log m) time. -/
def semijoinOn [TreeOrd Key] (leftKey : Left → Key)
    (rightKey : Right → Key) : Relation Left → Relation Right → Relation Left :=
  lift2 (fun left right ↦
      let keys := keySet rightKey right
      left.filter fun leftRow ↦ keys.contains (leftKey leftRow))
    fun _ _ _ _ sameLeft sameRight ↦ perm_filter sameLeft fun _ _ ↦ Bool.eq_iff_iff.mpr (by
      simp only [← Std.ExtTreeSet.mem_iff_contains, mem_keySet, sameRight.mem_iff])

/-- The left rows whose key no right row has, in O((n + m) log m) time. -/
def antijoinOn [TreeOrd Key] (leftKey : Left → Key)
    (rightKey : Right → Key) : Relation Left → Relation Right → Relation Left :=
  lift2 (fun left right ↦
      let keys := keySet rightKey right
      left.filter fun leftRow ↦ !keys.contains (leftKey leftRow))
    fun _ _ _ _ sameLeft sameRight ↦ perm_filter sameLeft fun _ _ ↦ Bool.eq_iff_iff.mpr (by
      simp only [Bool.not_eq_true', ← Bool.not_eq_true, ← Std.ExtTreeSet.mem_iff_contains,
        mem_keySet, sameRight.mem_iff])

section Keyed

variable [TreeOrd Key]

@[simp] theorem mem_joinOn {leftKey : Left → Key} {rightKey : Right → Key} {left : Relation Left}
    {right : Relation Right} {leftRow : Left} {rightRow : Right} :
    (leftRow, rightRow) ∈ joinOn leftKey rightKey left right ↔
      leftRow ∈ left ∧ rightRow ∈ right ∧ leftKey leftRow = rightKey rightRow := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right => exact mem_joinRows

@[simp] theorem mem_semijoinOn {leftKey : Left → Key} {rightKey : Right → Key}
    {left : Relation Left} {right : Relation Right} {leftRow : Left} :
    leftRow ∈ semijoinOn leftKey rightKey left right ↔
      leftRow ∈ left ∧ ∃ rightRow ∈ right, rightKey rightRow = leftKey leftRow := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right =>
    show leftRow ∈ left.filter (fun leftRow ↦ (keySet rightKey right).contains (leftKey leftRow)) ↔
      leftRow ∈ left ∧ ∃ rightRow, rightRow ∈ right ∧ _
    simp only [List.mem_filter, ← Std.ExtTreeSet.mem_iff_contains, mem_keySet]

@[simp] theorem mem_antijoinOn {leftKey : Left → Key} {rightKey : Right → Key}
    {left : Relation Left} {right : Relation Right} {leftRow : Left} :
    leftRow ∈ antijoinOn leftKey rightKey left right ↔
      leftRow ∈ left ∧ ∀ rightRow ∈ right, rightKey rightRow ≠ leftKey leftRow := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right =>
    show leftRow ∈ left.filter (fun leftRow ↦ !(keySet rightKey right).contains (leftKey leftRow)) ↔
      leftRow ∈ left ∧ ∀ rightRow, rightRow ∈ right → _
    simp only [List.mem_filter, Bool.not_eq_true', ← Bool.not_eq_true,
      ← Std.ExtTreeSet.mem_iff_contains, mem_keySet, not_exists, not_and]

end Keyed

/-! ### Counting -/

/-- The distinct elements of `rows`, keeping the last occurrence of each. -/
def distinctList [DecidableEq Row] : List Row → List Row
  | [] => []
  | row :: rest => if row ∈ rest then distinctList rest else row :: distinctList rest

theorem mem_distinctList [DecidableEq Row] {rows : List Row} {row : Row} :
    row ∈ distinctList rows ↔ row ∈ rows := by
  induction rows with
  | nil => simp [distinctList]
  | cons head rest ih =>
    unfold distinctList
    split
    · rename_i present
      rw [ih]
      constructor
      · exact List.mem_cons_of_mem _
      · intro member
        rcases List.mem_cons.mp member with rfl | later
        · exact present
        · exact later
    · simp [ih]

theorem nodup_distinctList [DecidableEq Row] (rows : List Row) : (distinctList rows).Nodup := by
  induction rows with
  | nil => simp [distinctList]
  | cons head rest ih =>
    unfold distinctList
    split
    · exact ih
    · rename_i absent
      exact List.nodup_cons.mpr ⟨fun member ↦ absent (mem_distinctList.mp member), ih⟩

/-- The number of rows, every repetition counted, in O(n) time; `distinct` first counts each row
once. -/
def count (relation : Relation Row) : Nat :=
  Quotient.liftOn relation List.length fun _ _ same ↦ same.length_eq

@[simp] theorem count_ofList {rows : List Row} : (ofList rows).count = rows.length := by rfl

theorem count_eq_zero {relation : Relation Row} : relation.count = 0 ↔ ∀ row, row ∉ relation := by
  induction relation using inductionOn with
  | ofList rows =>
    show rows.length = 0 ↔ ∀ row, row ∉ rows
    rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]

/-- How often `row` occurs, in O(n) time. -/
def multiplicity [DecidableEq Row] (row : Row) (relation : Relation Row) : Nat :=
  Quotient.liftOn relation (·.count row) fun _ _ same ↦ same.count_eq row

@[simp] theorem multiplicity_ofList [DecidableEq Row] {row : Row} {rows : List Row} :
    (ofList rows).multiplicity row = rows.count row :=
  by rfl

theorem multiplicity_pos [DecidableEq Row] {row : Row} {relation : Relation Row} :
    0 < relation.multiplicity row ↔ row ∈ relation := by
  induction relation using inductionOn with
  | ofList rows => exact List.count_pos_iff

/-- Relations are equal exactly when every row occurs in them equally often. -/
theorem eq_iff_multiplicity [DecidableEq Row] {left right : Relation Row} :
    left = right ↔ ∀ row, left.multiplicity row = right.multiplicity row := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right =>
    rw [ofList_eq_ofList, List.perm_iff_count]
    rfl

instance [DecidableEq Row] : DecidableEq (Relation Row) := fun left right ↦
  Quotient.recOnSubsingleton₂ left right fun left right ↦
    decidable_of_iff (left.Perm right) (ofList_eq_ofList (left := left) (right := right)).symm

@[simp] theorem multiplicity_union [DecidableEq Row] {row : Row} {left right : Relation Row} :
    (left ∪ right).multiplicity row = left.multiplicity row + right.multiplicity row := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right => exact List.count_append

@[simp] theorem count_union {left right : Relation Row} :
    (left ∪ right).count = left.count + right.count := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right => exact List.length_append

@[simp] theorem count_project {projection : Row → Result} {relation : Relation Row} :
    (relation.project projection).count = relation.count := by
  induction relation using inductionOn with
  | ofList rows => exact List.length_map _

/-- The elements of a tree set, in order, without repetition. -/
theorem nodup_toList [TreeOrd Row] (rows : Std.ExtTreeSet Row TreeOrd.cmp) :
    rows.toList.Nodup :=
  Std.ExtTreeSet.ordered_toList.imp fun below same ↦ by
    subst same
    simp [Std.ReflCmp.compare_self] at below

/-- How `distinct` rids a list of repetition: `dedup` keeps every member of the list, once. -/
class Dedup (Row : Type) where
  dedup : List Row → List Row
  mem_dedup : ∀ {rows : List Row} {row : Row}, row ∈ dedup rows ↔ row ∈ rows
  nodup_dedup : ∀ rows : List Row, (dedup rows).Nodup

attribute [simp] Dedup.mem_dedup

/-- Rows without a lawful order lose their repetitions by comparing every pair, in O(n²) time. -/
instance (priority := low) Dedup.ofDecidableEq [DecidableEq Row] : Dedup Row where
  dedup := distinctList
  mem_dedup := mem_distinctList
  nodup_dedup := nodup_distinctList

/-- Rows with a tree order lose their repetitions through a tree, in O(n log n) time. -/
instance Dedup.ofTreeOrd [TreeOrd Row] : Dedup Row where
  dedup rows := (keySet id rows).toList
  mem_dedup := by simp [Std.ExtTreeSet.mem_toList, mem_keySet]
  nodup_dedup _ := nodup_toList _

/-- The same rows, each once (SQL's `DISTINCT`): through a tree where the rows have a lawful order,
and otherwise by comparing every pair. -/
def distinct [Dedup Row] : Relation Row → Relation Row :=
  lift1 Dedup.dedup fun _ _ same ↦
    (List.perm_ext_iff_of_nodup (Dedup.nodup_dedup _) (Dedup.nodup_dedup _)).mpr fun _ ↦ by
      simp [same.mem_iff]

@[simp] theorem mem_distinct [Dedup Row] {relation : Relation Row} {row : Row} :
    row ∈ relation.distinct ↔ row ∈ relation := by
  induction relation using inductionOn with
  | ofList rows => exact Dedup.mem_dedup

/-! ### Grouping -/

section Grouping

variable [TreeOrd Key]

/-- Each key of a row of `rows`, in the order of the tree, with the relation of the rows that have
it: the keys from one tree and the rows of each from another. -/
private def groups (key : Row → Key) (rows : List Row) : List (Key × Relation Row) :=
  let byKey := grouped key rows
  (keySet key rows).toList.map fun value ↦ (value, ofList (byKey.getD value []))

private theorem groups_eq {key : Row → Key} {rows : List Row} :
    groups key rows = (keySet key rows).toList.map fun value ↦
      (value, ofList (rows.filter fun row ↦ TreeOrd.cmp (key row) value == .eq)) := by
  simp only [groups, getD_grouped]

/-- The rows grouped by `key`: one row for each key that some row has, with the relation of the
rows that have it, repetitions kept.  One tree collects the keys and another the rows of each, in
O(n log n) time for n rows; `aggregateBy` reduces each group. -/
def groupBy (key : Row → Key) : Relation Row → Relation (Key × Relation Row) :=
  lift1 (groups key) fun left right same ↦ by
    rw [groups_eq, groups_eq]
    have : keySet key left = keySet key right := Std.ExtTreeSet.ext_mem fun value ↦ by
      simp only [mem_keySet, same.mem_iff]
    rw [this]
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro value _
    rw [sound (same.filter _)]

@[simp] theorem mem_groupBy {key : Row → Key} {relation : Relation Row} {value : Key}
    {group : Relation Row} :
    (value, group) ∈ relation.groupBy key ↔ (∃ row ∈ relation, key row = value) ∧
      group = relation.select fun row ↦ TreeOrd.cmp (key row) value == .eq := by
  induction relation using inductionOn with
  | ofList rows =>
    show (value, group) ∈ groups key rows ↔ _
    rw [groups_eq]
    simp only [List.mem_map, Std.ExtTreeSet.mem_toList, mem_keySet, Prod.mk.injEq]
    constructor
    · rintro ⟨other, found, rfl, rfl⟩
      exact ⟨found, rfl⟩
    · rintro ⟨found, rfl⟩
      exact ⟨value, found, rfl, rfl⟩

end Grouping

/-! ### Order as data: least and greatest rows by a column -/

/-- Filters of permuted lists, each by a predicate computed from its own list, are permuted when
the predicate holds of a member exactly when a statement about the members of the list does. -/
private theorem perm_filter_of_spec {test : List Row → Row → Bool} {spec : List Row → Row → Prop}
    (holds : ∀ {rows : List Row} {row : Row}, row ∈ rows → (test rows row = true ↔ spec rows row))
    (respects : ∀ {rows other : List Row}, SameMembers rows other → ∀ row, spec rows row ↔ spec other row)
    {left right : List Row} (same : left.Perm right) :
    (left.filter (test left)).Perm (right.filter (test right)) :=
  perm_filter same fun row member ↦ Bool.eq_iff_iff.mpr
    ((holds member).trans ((respects same.sameMembers row).trans
      (holds (same.mem_iff.mp member)).symm))

/-- The least key of `rows` under `cmp`. -/
private def leastKey (cmp : Key → Key → Ordering) (key : Row → Key) : List Row → Option Key
  | [] => none
  | row :: rest =>
    match leastKey cmp key rest with
    | none => some (key row)
    | some least => if (cmp (key row) least).isLE then some (key row) else some least

private theorem leastKey_eq_none {cmp : Key → Key → Ordering} {key : Row → Key} :
    ∀ {rows : List Row}, leastKey cmp key rows = none → rows = []
  | [], _ => rfl
  | _ :: _, found => by
    unfold leastKey at found
    split at found
    · cases found
    · split at found <;> cases found

private theorem leastKey_spec {cmp : Key → Key → Ordering} [Std.TransCmp cmp] {key : Row → Key} :
    ∀ {rows : List Row} {least : Key}, leastKey cmp key rows = some least →
      (∃ row ∈ rows, key row = least) ∧ ∀ row ∈ rows, (cmp least (key row)).isLE
  | [], _, found => by simp [leastKey] at found
  | row :: rest, least, found => by
    cases previous : leastKey cmp key rest with
    | none =>
      have empty := leastKey_eq_none previous
      subst empty
      simp only [leastKey, Option.some.injEq] at found
      subst found
      simp [Std.ReflCmp.isLE_rfl]
    | some previousLeast =>
      obtain ⟨⟨witness, witnessMember, witnessKey⟩, below⟩ := leastKey_spec previous
      simp only [leastKey, previous] at found
      by_cases smaller : (cmp (key row) previousLeast).isLE = true
      · simp only [smaller, ite_true, Option.some.injEq] at found
        subst found
        refine ⟨⟨row, List.mem_cons_self, rfl⟩, fun other member ↦ ?_⟩
        rcases List.mem_cons.mp member with rfl | later
        · exact Std.ReflCmp.isLE_rfl
        · exact Std.TransCmp.isLE_trans smaller (below other later)
      · simp only [smaller, Bool.false_eq_true, ite_false, Option.some.injEq] at found
        subst found
        refine ⟨⟨witness, List.mem_cons_of_mem _ witnessMember, witnessKey⟩,
          fun other member ↦ ?_⟩
        rcases List.mem_cons.mp member with rfl | later
        · have greater : cmp (key other) previousLeast = .gt := by
            cases compared : cmp (key other) previousLeast <;> simp_all
          simp [Std.OrientedCmp.lt_of_gt greater]
        · exact below other later

/-- Whether `row`'s key is the least key of `rows` under `cmp`. -/
private def atLeast (cmp : Key → Key → Ordering) (key : Row → Key) (rows : List Row) (row : Row) :
    Bool :=
  match leastKey cmp key rows with
  | none => false
  | some least => (cmp (key row) least).isLE

/-- The rows of `rows` whose key is least under `cmp`. -/
private def leastRows (cmp : Key → Key → Ordering) (key : Row → Key) (rows : List Row) :
    List Row :=
  rows.filter (atLeast cmp key rows)

private theorem mem_leastRows {cmp : Key → Key → Ordering} [Std.TransCmp cmp] {key : Row → Key}
    {rows : List Row} {row : Row} :
    row ∈ leastRows cmp key rows ↔ row ∈ rows ∧ ∀ other ∈ rows, (cmp (key row) (key other)).isLE := by
  unfold leastRows atLeast
  cases found : leastKey cmp key rows with
  | none => simp [leastKey_eq_none found]
  | some least =>
    obtain ⟨⟨witness, witnessMember, witnessKey⟩, below⟩ := leastKey_spec found
    simp only [List.mem_filter, and_congr_right_iff]
    intro _
    constructor
    · intro atMost other member
      exact Std.TransCmp.isLE_trans atMost (below other member)
    · intro atMost
      exact witnessKey ▸ atMost witness witnessMember

/-- The rows whose `key` is least under `cmp`, in O(n) time.  Rows that tie are all kept. -/
private def leastBy (cmp : Key → Key → Ordering) [Std.TransCmp cmp] (key : Row → Key) :
    Relation Row → Relation Row :=
  lift1 (leastRows cmp key) fun _ _ same ↦
    perm_filter_of_spec (test := atLeast cmp key)
      (spec := fun rows row ↦ ∀ other ∈ rows, (cmp (key row) (key other)).isLE)
      (fun {rows row} member ↦ by
        have := mem_leastRows (cmp := cmp) (key := key) (rows := rows) (row := row)
        simp only [leastRows, List.mem_filter] at this
        exact ⟨fun atMost ↦ (this.mp ⟨member, atMost⟩).2, fun least ↦ (this.mpr ⟨member, least⟩).2⟩)
      (fun same _ ↦ forall_congr' fun other ↦ imp_congr_left (same other)) same

@[simp] private theorem mem_leastBy {cmp : Key → Key → Ordering} [Std.TransCmp cmp] {key : Row → Key}
    {relation : Relation Row} {row : Row} :
    row ∈ leastBy cmp key relation ↔
      row ∈ relation ∧ ∀ other ∈ relation, (cmp (key row) (key other)).isLE := by
  induction relation using inductionOn with
  | ofList rows => exact mem_leastRows

/-- The rows with the least `key`, as "first" by a sequence column, in O(n) time.  Rows that tie
are all kept; `the?` picks the row when there is one. -/
def minBy [Ord Key] [Std.TransOrd Key] (key : Row → Key) :
    Relation Row → Relation Row :=
  leastBy compare key

/-- The rows with the greatest `key`, as "latest" by a sequence column, in O(n) time. -/
def maxBy [Ord Key] [Std.TransOrd Key] (key : Row → Key) :
    Relation Row → Relation Row :=
  leastBy (fun left right ↦ compare right left) key

@[simp] theorem mem_minBy [Ord Key] [Std.TransOrd Key] {key : Row → Key}
    {relation : Relation Row}
    {row : Row} :
    row ∈ minBy key relation ↔
      row ∈ relation ∧ ∀ other ∈ relation, (compare (key row) (key other)).isLE :=
  mem_leastBy

@[simp] theorem mem_maxBy [Ord Key] [Std.TransOrd Key] {key : Row → Key}
    {relation : Relation Row}
    {row : Row} :
    row ∈ maxBy key relation ↔
      row ∈ relation ∧ ∀ other ∈ relation, (compare (key other) (key row)).isLE :=
  mem_leastBy

/-- For each value of `group`, the greatest value of `key` among the rows of `rows` with it. -/
private def greatest {Group : Type} [TreeOrd Group] [Ord Key] (group : Row → Group)
    (key : Row → Key) (rows : List Row) : Std.ExtTreeMap Group Key TreeOrd.cmp :=
  rows.foldr (fun row best ↦
    match best[group row]? with
    | some current => if (compare current (key row)).isLE then best.insert (group row) (key row) else best
    | none => best.insert (group row) (key row)) ∅

/-- What `greatest` holds for a group: the key of one of its rows, at least the key of every row
of the group; and nothing for a group without rows. -/
private def Greatest {Group : Type} [Ord Key] (group : Row → Group) (key : Row → Key)
    (rows : List Row) (value : Group) : Option Key → Prop
  | some best => (∃ row ∈ rows, group row = value ∧ key row = best) ∧
      ∀ row ∈ rows, group row = value → (compare (key row) best).isLE
  | none => ∀ row ∈ rows, group row ≠ value

private theorem greatest_spec {Group : Type} [TreeOrd Group]
    [Ord Key] [Std.TransOrd Key] {group : Row → Group} {key : Row → Key} :
    ∀ (rows : List Row) (value : Group), Greatest group key rows value (greatest group key rows)[value]?
  | [], value => by simp [greatest, Greatest]
  | head :: rest, value => by
    have previous := greatest_spec (group := group) (key := key) rest
    have unfolded : greatest group key (head :: rest) =
        match (greatest group key rest)[group head]? with
        | some current => if (compare current (key head)).isLE then
            (greatest group key rest).insert (group head) (key head) else greatest group key rest
        | none => (greatest group key rest).insert (group head) (key head) := rfl
    have atHead : ∀ found, (greatest group key rest)[group head]? = found →
        Greatest group key rest (group head) found := fun found same ↦ same ▸ previous (group head)
    rw [unfolded]
    -- Inserting `key head` for the group of `head`, given that it is at least every key there.
    have inserted : (∀ row ∈ rest, group row = group head → (compare (key row) (key head)).isLE) →
        Greatest group key (head :: rest) value
          ((greatest group key rest).insert (group head) (key head))[value]? := by
      intro above
      rw [Std.ExtTreeMap.getElem?_insert]
      split
      · rename_i same
        have same := Std.LawfulEqCmp.eq_of_compare same
        subst same
        refine ⟨⟨head, List.mem_cons_self, rfl, rfl⟩, fun row member same ↦ ?_⟩
        rcases List.mem_cons.mp member with rfl | later
        · exact Std.ReflCmp.isLE_rfl
        · exact above row later same
      · rename_i differs
        have other : group head ≠ value := fun same ↦ differs (same ▸ Std.ReflCmp.compare_self)
        have := previous value
        revert this
        cases (greatest group key rest)[value]? with
        | none =>
          intro absent row member
          rcases List.mem_cons.mp member with rfl | later
          · exact other
          · exact absent row later
        | some best =>
          rintro ⟨⟨witness, member, same, rfl⟩, below⟩
          refine ⟨⟨witness, List.mem_cons_of_mem _ member, same, rfl⟩, fun row member same ↦ ?_⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact absurd same other
          · exact below row later same
    split
    · rename_i current found
      obtain ⟨⟨witness, witnessMember, witnessGroup, rfl⟩, below⟩ := atHead _ found
      split
      · rename_i atMost
        exact inserted fun row member same ↦
          Std.TransCmp.isLE_trans (below row member same) atMost
      · rename_i greater
        have headBelow : (compare (key head) (key witness)).isLE := by
          cases compared : compare (key witness) (key head) <;>
            simp_all [Std.OrientedCmp.lt_of_gt (cmp := compare)]
        have := previous value
        revert this
        by_cases same : group head = value
        · subst same
          rw [found]
          rintro ⟨_, _⟩
          refine ⟨⟨witness, List.mem_cons_of_mem _ witnessMember, witnessGroup, rfl⟩,
            fun row member same ↦ ?_⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact headBelow
          · exact below row later same
        · cases (greatest group key rest)[value]? with
          | none =>
            intro absent row member
            rcases List.mem_cons.mp member with rfl | later
            · exact same
            · exact absent row later
          | some best =>
            rintro ⟨⟨other, member, otherGroup, rfl⟩, otherBelow⟩
            refine ⟨⟨other, List.mem_cons_of_mem _ member, otherGroup, rfl⟩,
              fun row member rowGroup ↦ ?_⟩
            rcases List.mem_cons.mp member with rfl | later
            · exact absurd rowGroup same
            · exact otherBelow row later rowGroup
    · rename_i absent
      exact inserted fun row member same ↦ absurd same (atHead none absent row member)

/-- Whether `row`'s key is the greatest among the rows of `rows` with its value of `group`. -/
private def atGreatest {Group : Type} [TreeOrd Group] [Ord Key]
    (group : Row → Group) (key : Row → Key) (rows : List Row) (row : Row) : Bool :=
  match (greatest group key rows)[group row]? with
  | some top => (compare top (key row)).isLE
  | none => false

/-- The rows of `rows` whose `key` is greatest among the rows with their value of `group`. -/
private def greatestRows {Group : Type} [TreeOrd Group] [Ord Key]
    (group : Row → Group) (key : Row → Key) (rows : List Row) : List Row :=
  rows.filter (atGreatest group key rows)

private theorem mem_greatestRows {Group : Type} [TreeOrd Group]
    [Ord Key] [Std.TransOrd Key] {group : Row → Group} {key : Row → Key}
    {rows : List Row} {row : Row} :
    row ∈ greatestRows group key rows ↔ row ∈ rows ∧
      ∀ other ∈ rows, group other = group row → (compare (key other) (key row)).isLE := by
  simp only [greatestRows, atGreatest, List.mem_filter, and_congr_right_iff]
  intro member
  have := greatest_spec (group := group) (key := key) rows (group row)
  revert this
  cases (greatest group key rows)[group row]? with
  | none =>
    intro absent
    exact absurd rfl (absent row member)
  | some top =>
    rintro ⟨⟨witness, witnessMember, witnessGroup, rfl⟩, below⟩
    constructor
    · intro atMost other otherMember same
      exact Std.TransCmp.isLE_trans (below other otherMember same) atMost
    · intro above
      exact above witness witnessMember witnessGroup

/-- For each value of `group`, the rows with it whose `key` is greatest: the latest event per
key, or the latest row per record, by a sequence column.  Rows that tie are all kept.  One pass
collects the greatest key of every group in a balanced tree, in O(n log n) time for n rows. -/
def maxByGroup {Group : Type} [TreeOrd Group] [Ord Key]
    [Std.TransOrd Key] (group : Row → Group) (key : Row → Key) :
    Relation Row → Relation Row :=
  lift1 (greatestRows group key) fun _ _ same ↦
    perm_filter_of_spec (test := atGreatest group key)
      (spec := fun rows row ↦
        ∀ other ∈ rows, group other = group row → (compare (key other) (key row)).isLE)
      (fun {rows row} member ↦ by
        have := mem_greatestRows (group := group) (key := key) (rows := rows) (row := row)
        simp only [greatestRows, List.mem_filter] at this
        exact ⟨fun top ↦ (this.mp ⟨member, top⟩).2, fun greatest ↦ (this.mpr ⟨member, greatest⟩).2⟩)
      (fun same _ ↦ forall_congr' fun other ↦ imp_congr_left (same other)) same

@[simp] theorem mem_maxByGroup {Group : Type} [TreeOrd Group]
    [Ord Key] [Std.TransOrd Key] {group : Row → Group}
    {key : Row → Key}
    {relation : Relation Row} {row : Row} :
    row ∈ maxByGroup group key relation ↔ row ∈ relation ∧
      ∀ other ∈ relation, group other = group row → (compare (key other) (key row)).isLE := by
  induction relation using inductionOn with
  | ofList rows => exact mem_greatestRows

/-- The row of a relation with exactly one row. -/
private def onlyRow [DecidableEq Row] : List Row → Option Row
  | [] => none
  | row :: rest => if rest.all (· == row) then some row else none

private theorem onlyRow_eq_some [DecidableEq Row] {rows : List Row} {row : Row} :
    onlyRow rows = some row ↔ row ∈ rows ∧ ∀ other ∈ rows, other = row := by
  cases rows with
  | nil => simp [onlyRow]
  | cons head rest =>
    simp only [onlyRow]
    by_cases all : (rest.all fun other ↦ other == head) = true
    · simp only [all, ite_true, Option.some.injEq]
      simp only [List.all_eq_true, beq_iff_eq] at all
      constructor
      · rintro rfl
        exact ⟨List.mem_cons_self, fun other member ↦ by
          rcases List.mem_cons.mp member with rfl | later
          · rfl
          · exact all other later⟩
      · rintro ⟨_, every⟩
        exact every head List.mem_cons_self
    · simp only [all, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff]
      rintro ⟨_, every⟩
      apply all
      simp only [List.all_eq_true, beq_iff_eq]
      intro other member
      exact (every other (List.mem_cons_of_mem _ member)).trans (every head List.mem_cons_self).symm

/-- The row of a relation that has rows and whose rows are all that one row, once or repeated, and
`none` otherwise, in O(n) time. -/
def the? [DecidableEq Row] (relation : Relation Row) : Option Row :=
  Quotient.liftOn relation onlyRow fun left right perm ↦ by
    have same := perm.sameMembers
    cases found : onlyRow right with
    | none =>
      cases found' : onlyRow left with
      | none => rfl
      | some row =>
        have := onlyRow_eq_some.mp found'
        have : onlyRow right = some row := onlyRow_eq_some.mpr
          ⟨(same row).mp this.1, fun other member ↦ this.2 other ((same other).mpr member)⟩
        simp_all
    | some row =>
      have := onlyRow_eq_some.mp found
      exact onlyRow_eq_some.mpr
        ⟨(same row).mpr this.1, fun other member ↦ this.2 other ((same other).mp member)⟩

theorem the?_eq_some [DecidableEq Row] {relation : Relation Row} {row : Row} :
    relation.the? = some row ↔ row ∈ relation ∧ ∀ other ∈ relation, other = row := by
  induction relation using inductionOn with
  | ofList rows => exact onlyRow_eq_some

/-! ### Keys, references and inclusion -/

/-- No two rows share a key, a repeated row counted as often as it repeats: `Keyed id` says that
no row repeats. -/
@[expose] def Keyed (relation : Relation Row) (key : Row → Key) : Prop :=
  Quotient.liftOn relation (fun rows ↦ Relational.Keyed rows key) fun _ _ same ↦
    propext (same.map key).nodup_iff

theorem keyed_ofList {rows : List Row} {key : Row → Key} :
    (ofList rows).Keyed key ↔ Relational.Keyed rows key :=
  Iff.rfl

/-- Every child's reference is some parent's key. -/
@[expose] def References {Child Parent : Type} (children : Relation Child) (reference : Child → Key)
    (parents : Relation Parent) (key : Parent → Key) : Prop :=
  ∀ child ∈ children, ∃ parent ∈ parents, key parent = reference child

/-- Every row of `previous` is a row of `next`. -/
@[expose] def Included (previous next : Relation Row) : Prop := ∀ row ∈ previous, row ∈ next

/-- Rows with distinct keys are distinct and keyed. -/
private theorem keyedSet_of_keyed {key : Row → Key} :
    ∀ {rows : List Row}, Relational.Keyed rows key →
      ∀ left ∈ rows, ∀ right ∈ rows, key left = key right → left = right
  | [], _ => by simp
  | row :: rest, keyed => by
    simp only [Relational.Keyed, List.map_cons, List.nodup_cons, List.mem_map, not_exists,
      not_and] at keyed
    obtain ⟨fresh, keyedRest⟩ := keyed
    intro left leftMember right rightMember same
    rcases List.mem_cons.mp leftMember with rfl | leftLater <;>
      rcases List.mem_cons.mp rightMember with rfl | rightLater
    · rfl
    · exact absurd same.symm (fresh right rightLater)
    · exact absurd same (fresh left leftLater)
    · exact keyedSet_of_keyed keyedRest left leftLater right rightLater same

/-- Rows of a keyed relation that share a key are the same row. -/
theorem Keyed.eq_of_key {relation : Relation Row} {key : Row → Key} (keyed : relation.Keyed key)
    {left right : Row} (leftMember : left ∈ relation) (rightMember : right ∈ relation)
    (same : key left = key right) : left = right := by
  induction relation using inductionOn with
  | ofList rows => exact keyedSet_of_keyed keyed left leftMember right rightMember same

/-- A list is keyed by `key` exactly when it repeats no row and its rows that share a key are the
same row. -/
private theorem keyed_iff_list {key : Row → Key} : ∀ {rows : List Row},
    Relational.Keyed rows key ↔
      rows.Nodup ∧ ∀ left ∈ rows, ∀ right ∈ rows, key left = key right → left = right
  | [] => by simp [Relational.Keyed]
  | head :: rest => by
    have ih := keyed_iff_list (key := key) (rows := rest)
    constructor
    · intro keyed
      refine ⟨?_, keyedSet_of_keyed keyed⟩
      simp only [Relational.Keyed, List.map_cons, List.nodup_cons, List.mem_map, not_exists,
        not_and] at keyed
      exact List.nodup_cons.mpr ⟨fun member ↦ keyed.1 head member rfl, (ih.mp keyed.2).1⟩
    · rintro ⟨distinct, injective⟩
      have ⟨fresh, rest'⟩ := List.nodup_cons.mp distinct
      simp only [Relational.Keyed, List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      refine ⟨fun other member same ↦ fresh ?_, ih.mpr ⟨rest', fun left leftMember right rightMember ↦
        injective left (List.mem_cons_of_mem _ leftMember) right (List.mem_cons_of_mem _ rightMember)⟩⟩
      exact (injective other (List.mem_cons_of_mem _ member) head List.mem_cons_self same) ▸ member

/-- A relation is keyed by `key` exactly when no row repeats and rows that share a key are the same
row. -/
theorem keyed_iff_mem {relation : Relation Row} {key : Row → Key} :
    relation.Keyed key ↔
      relation.Keyed id ∧ ∀ left ∈ relation, ∀ right ∈ relation, key left = key right → left = right := by
  induction relation using inductionOn with
  | ofList rows =>
    show Relational.Keyed rows key ↔ Relational.Keyed rows id ∧ ∀ left ∈ rows, ∀ right ∈ rows, _
    rw [keyed_iff_list, keyed_iff_list]
    constructor
    · rintro ⟨distinct, injective⟩
      exact ⟨⟨distinct, fun _ _ _ _ same ↦ same⟩, injective⟩
    · rintro ⟨⟨distinct, _⟩, injective⟩
      exact ⟨distinct, injective⟩

/-- `Keyed`, decided on the list behind the relation in one pass through a hash set of the keys,
or by comparing the keys of every pair for a small relation. -/
def keyed [DecidableEq Key] [Hashable Key] (relation : Relation Row) (key : Row → Key) : Bool :=
  Quotient.liftOn relation (fun rows ↦ keyedFast rows key) fun left right same ↦ by
    apply Bool.eq_iff_iff.mpr
    rw [keyedFast_iff, keyedFast_iff]
    exact (same.map key).nodup_iff

theorem keyed_iff [DecidableEq Key] [Hashable Key] {relation : Relation Row} {key : Row → Key} :
    relation.keyed key = true ↔ relation.Keyed key := by
  induction relation using inductionOn with
  | ofList rows => exact keyedFast_iff rows key

instance [DecidableEq Key] [Hashable Key] (relation : Relation Row) (key : Row → Key) :
    Decidable (relation.Keyed key) :=
  decidable_of_iff _ keyed_iff

/-- Relations without repeated rows and with the same members are equal. -/
theorem ext {left right : Relation Row} (leftDistinct : left.Keyed id)
    (rightDistinct : right.Keyed id) (same : ∀ row, row ∈ left ↔ row ∈ right) : left = right := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right =>
    apply sound
    apply (List.perm_ext_iff_of_nodup _ _).mpr same
    · simpa [Relational.Keyed] using keyed_ofList.mp leftDistinct
    · simpa [Relational.Keyed] using keyed_ofList.mp rightDistinct

/-- `distinct` leaves no row repeated. -/
theorem distinct_keyed [Dedup Row] {relation : Relation Row} : relation.distinct.Keyed id := by
  induction relation using inductionOn with
  | ofList rows =>
    show Relational.Keyed (Dedup.dedup rows) id
    simpa [Relational.Keyed] using Dedup.nodup_dedup rows

/-- `distinct` changes nothing in a relation that repeats no row. -/
theorem distinct_eq_of_keyed [Dedup Row] {relation : Relation Row} (distinct : relation.Keyed id) :
    relation.distinct = relation :=
  ext distinct_keyed distinct fun _ ↦ mem_distinct

/-- The rows a selection keeps keep the keys of the relation distinct. -/
theorem Keyed.select {relation : Relation Row} {key : Row → Key} {predicate : Row → Bool}
    (keyed : relation.Keyed key) : (relation.select predicate).Keyed key := by
  induction relation using inductionOn with
  | ofList rows => exact ((List.filter_sublist).map key).nodup keyed

/-- A relation keyed by `key` is keyed by any `other` from which `key` can be computed (`recovers`):
rows that share `other` share `key`, and are one row. -/
theorem Keyed.of_recovers {K : Type} {relation : Relation Row} {key : Row → Key} {other : Row → K}
    (keyed : relation.Keyed key) (recover : K → Key) (recovers : ∀ row, recover (other row) = key row) :
    relation.Keyed other :=
  keyed_iff_mem.mpr ⟨(keyed_iff_mem.mp keyed).1, fun left leftMember right rightMember same ↦
    keyed.eq_of_key leftMember rightMember (by rw [← recovers left, ← recovers right, same])⟩

/-- The rows of one group of a relation keyed by a group and `key` together, such as one record's
rows of a table keyed by record and element, are keyed by `key` alone: the rows a selection keeps
(`predicate`) that are all of the group `wanted` (`within`). -/
theorem Keyed.select_group {Group : Type} {relation : Relation Row} {group : Row → Group} {key : Row → Key}
    (keyed : relation.Keyed fun row ↦ (group row, key row)) {predicate : Row → Bool} {wanted : Group}
    (within : ∀ row, predicate row = true → group row = wanted) : (relation.select predicate).Keyed key :=
  keyed_iff_mem.mpr ⟨(keyed_iff_mem.mp keyed.select).1, fun left leftMember right rightMember same ↦ by
    simp only [mem_select] at leftMember rightMember
    exact keyed.eq_of_key leftMember.1 rightMember.1
      (by rw [within left leftMember.2, within right rightMember.2, same])⟩

/-- The rows a semijoin keeps keep the keys of the relation distinct. -/
theorem Keyed.semijoinOn {Join : Type} [TreeOrd Join] {left : Relation Left} {right : Relation Right}
    {key : Left → Key} {leftKey : Left → Join} {rightKey : Right → Join} (keyed : left.Keyed key) :
    (semijoinOn leftKey rightKey left right).Keyed key := by
  induction left using inductionOn with
  | ofList lefts =>
  induction right using inductionOn with
  | ofList rights => exact ((List.filter_sublist).map key).nodup keyed

/-- `maxByGroup` keeps a subset of the rows, so a relation keyed by `key` stays keyed by it. -/
theorem Keyed.maxByGroup {Group Order K : Type} [Ord Group] [Std.TransOrd Group] [Std.LawfulEqOrd Group]
    [Ord Order] [Std.TransOrd Order] {relation : Relation Row} {key : Row → K} {group : Row → Group}
    {order : Row → Order} (keyed : relation.Keyed key) : (relation.maxByGroup group order).Keyed key := by
  induction relation using inductionOn with
  | ofList rows => exact ((List.filter_sublist).map key).nodup keyed

/-- `References`, decided on the lists behind the relations through a hash set of the parents'
keys, in O(n + m) expected time. -/
def references {Child Parent : Type} [DecidableEq Key] [Hashable Key] (children : Relation Child)
    (reference : Child → Key) (parents : Relation Parent) (key : Parent → Key) : Bool :=
  Quotient.liftOn₂ children parents (fun children parents ↦
      referencesFast children reference parents key) fun children parents children' parents'
        permChildren permParents ↦ by
    have sameChildren := permChildren.sameMembers
    have sameParents := permParents.sameMembers
    apply Bool.eq_iff_iff.mpr
    simp only [referencesFast_iff, Relational.References]
    constructor <;> intro holds child member
    · obtain ⟨parent, parentMember, agrees⟩ := holds child ((sameChildren child).mpr member)
      exact ⟨parent, (sameParents parent).mp parentMember, agrees⟩
    · obtain ⟨parent, parentMember, agrees⟩ := holds child ((sameChildren child).mp member)
      exact ⟨parent, (sameParents parent).mpr parentMember, agrees⟩

theorem references_iff {Child Parent : Type} [DecidableEq Key] [Hashable Key]
    {children : Relation Child} {reference : Child → Key} {parents : Relation Parent}
    {key : Parent → Key} :
    references children reference parents key = true ↔
      References children reference parents key := by
  induction children using inductionOn with
  | ofList children =>
  induction parents using inductionOn with
  | ofList parents => exact referencesFast_iff _ _ _ _

instance {Child Parent : Type} [DecidableEq Key] [Hashable Key] (children : Relation Child)
    (reference : Child → Key) (parents : Relation Parent) (key : Parent → Key) :
    Decidable (References children reference parents key) :=
  decidable_of_iff _ references_iff

instance [DecidableEq Row] (previous next : Relation Row) : Decidable (Included previous next) :=
  decidable_of_iff (previous.all fun row ↦ decide (row ∈ next)) (by simp [Included])

/-! ### Extraction, sorted by a column -/

/-- Whether each key is less than the next one. -/
private def ascending [Ord Key] (key : Row → Key) : List Row → Bool
  | [] | [_] => true
  | first :: second :: rest =>
    compare (key first) (key second) == .lt && ascending key (second :: rest)

private theorem pairwise_of_ascending [Ord Key] [Std.TransOrd Key] {key : Row → Key} :
    ∀ {rows : List Row}, ascending key rows = true →
      rows.Pairwise fun left right ↦ compare (key left) (key right) = .lt
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | first :: second :: rest, holds => by
    simp only [ascending, Bool.and_eq_true, beq_iff_eq] at holds
    have tail := pairwise_of_ascending holds.2
    refine List.Pairwise.cons (fun other member ↦ ?_) tail
    rcases List.mem_cons.mp member with rfl | later
    · exact holds.1
    · exact Std.TransCmp.lt_trans holds.1 (List.rel_of_pairwise_cons tail later)

private theorem ascending_of_pairwise [Ord Key] {key : Row → Key} :
    ∀ {rows : List Row}, (rows.Pairwise fun left right ↦ compare (key left) (key right) = .lt) →
      ascending key rows = true
  | [], _ => rfl
  | [_], _ => rfl
  | first :: second :: rest, pairwise => by
    simp only [ascending, Bool.and_eq_true, beq_iff_eq]
    exact ⟨List.rel_of_pairwise_cons pairwise List.mem_cons_self,
      ascending_of_pairwise pairwise.of_cons⟩

private theorem ne_head_of_ascending [Ord Key] [Std.TransOrd Key] {key : Row → Key}
    {head row : Row} {rows : List Row}
    (sorted : (head :: rows).Pairwise fun first second ↦ compare (key first) (key second) = .lt)
    (member : row ∈ rows) : row ≠ head := by
  rintro rfl
  have := List.rel_of_pairwise_cons sorted member
  simp [Std.ReflCmp.compare_self] at this

/-- Lists sorted strictly by key with the same members are equal. -/
private theorem eq_of_ascending [Ord Key] [Std.TransOrd Key] {key : Row → Key} :
    ∀ {left right : List Row},
      (left.Pairwise fun first second ↦ compare (key first) (key second) = .lt) →
      (right.Pairwise fun first second ↦ compare (key first) (key second) = .lt) →
      SameMembers left right → left = right
  | [], [], _, _, _ => rfl
  | [], row :: _, _, _, same => absurd ((same row).mpr List.mem_cons_self) (by simp)
  | row :: _, [], _, _, same => absurd ((same row).mp List.mem_cons_self) (by simp)
  | first :: left, second :: right, leftSorted, rightSorted, same => by
    have irreflexive : ∀ row : Row, compare (key row) (key row) ≠ .lt := fun row ↦ by
      simp [Std.ReflCmp.compare_self]
    have heads : first = second := by
      rcases List.mem_cons.mp ((same first).mp List.mem_cons_self) with equal | firstLater
      · exact equal
      rcases List.mem_cons.mp ((same second).mpr List.mem_cons_self) with equal | secondLater
      · exact equal.symm
      have below := List.rel_of_pairwise_cons leftSorted secondLater
      have above := List.rel_of_pairwise_cons rightSorted firstLater
      exact absurd (Std.TransCmp.lt_trans below above) (irreflexive first)
    subst heads
    congr 1
    apply eq_of_ascending leftSorted.of_cons rightSorted.of_cons
    intro row
    constructor
    · intro member
      rcases List.mem_cons.mp ((same row).mp (List.mem_cons_of_mem _ member)) with equal | later
      · exact absurd equal (ne_head_of_ascending leftSorted member)
      · exact later
    · intro member
      rcases List.mem_cons.mp ((same row).mpr (List.mem_cons_of_mem _ member)) with equal | later
      · exact absurd equal (ne_head_of_ascending rightSorted member)
      · exact later

/-- The rows sorted by key, if no two of them share a key: sorted, and then checked to be in strictly
ascending order of key. -/
private def sortedRows [Ord Key] (key : Row → Key) (rows : List Row) : Option (List Row) :=
  let sorted := rows.mergeSort fun left right ↦ (compare (key left) (key right)).isLE
  if ascending key sorted then some sorted else none

private theorem sortedRows_some [Ord Key] [Std.TransOrd Key] {key : Row → Key}
    {rows sorted : List Row} (found : sortedRows key rows = some sorted) :
    sorted.Perm rows ∧ sorted.Pairwise fun left right ↦ compare (key left) (key right) = .lt := by
  dsimp only [sortedRows] at found
  split at found
  · rename_i holds
    cases found
    exact ⟨List.mergeSort_perm _ _, pairwise_of_ascending holds⟩
  · cases found

private theorem sortedRows_isSome [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key]
    {key : Row → Key} {rows : List Row} : (sortedRows key rows).isSome ↔ Relational.Keyed rows key := by
  unfold sortedRows
  generalize sortedIs : rows.mergeSort
    (fun left right ↦ (compare (key left) (key right)).isLE) = sorted
  have same : sorted.Perm rows := sortedIs ▸ List.mergeSort_perm _ _
  have sortedLE : sorted.Pairwise fun left right ↦ (compare (key left) (key right)).isLE := by
    rw [← sortedIs]
    exact List.pairwise_mergeSort (le := fun left right ↦ (compare (key left) (key right)).isLE)
      (fun _ _ _ first second ↦ Std.TransCmp.isLE_trans (cmp := compare) first second)
      (fun first second ↦ by
        cases compared : compare (key first) (key second)
        · simp
        · simp
        · simp [Std.OrientedCmp.lt_of_gt compared])
      _
  rw [show Relational.Keyed rows key ↔ Relational.Keyed sorted key from (same.map key).nodup_iff.symm]
  simp only [Relational.Keyed]
  constructor
  · intro holds
    split at holds
    · rename_i ascends
      exact List.pairwise_map.mpr ((pairwise_of_ascending ascends).imp fun below equal ↦ by
        simp [equal, Std.ReflCmp.compare_self] at below)
    · simp at holds
  · intro distinct
    have ascends : ascending key sorted = true := ascending_of_pairwise
      ((sortedLE.and (List.pairwise_map.mp distinct)).imp fun ⟨atMost, differ⟩ ↦ by
        cases compared : compare (key _) (key _)
        · rfl
        · exact absurd (Std.LawfulEqCmp.eq_of_compare compared) differ
        · simp [compared] at atMost)
    simp [ascends]

/-- The rows in ascending order of `key`, if no two rows share a key (a repeated row sharing its
own), and `none` otherwise.  This is the only way to read rows out of a relation in an order, and
the order is that of a column. -/
def sortedBy? [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key] (key : Row → Key)
    (relation : Relation Row) : Option (Array Row) :=
  Quotient.liftOn relation (fun rows ↦ (sortedRows key rows).map List.toArray)
    fun left right same ↦ by
      have keyedSame : Relational.Keyed left key ↔ Relational.Keyed right key := (same.map key).nodup_iff
      cases leftFound : sortedRows key left with
      | none =>
        cases rightFound : sortedRows key right with
        | none => rfl
        | some _ =>
          have := sortedRows_isSome.mpr (keyedSame.mpr
            (sortedRows_isSome.mp (by simp [rightFound] : (sortedRows key right).isSome)))
          simp [leftFound] at this
      | some leftSorted =>
        cases rightFound : sortedRows key right with
        | none =>
          have := sortedRows_isSome.mpr (keyedSame.mp
            (sortedRows_isSome.mp (by simp [leftFound] : (sortedRows key left).isSome)))
          simp [rightFound] at this
        | some rightSorted =>
          obtain ⟨leftSame, leftAscending⟩ := sortedRows_some leftFound
          obtain ⟨rightSame, rightAscending⟩ := sortedRows_some rightFound
          have : leftSorted = rightSorted := eq_of_ascending leftAscending rightAscending
            (leftSame.trans (same.trans rightSame.symm)).sameMembers
          simp [this]

/-- What `sortedBy?` returns has the relation's rows, in ascending order of `key`. -/
theorem sortedBy?_eq_some [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key]
    {key : Row → Key} {relation : Relation Row} {sorted : Array Row}
    (found : relation.sortedBy? key = some sorted) :
    (∀ row, row ∈ sorted ↔ row ∈ relation) ∧
      sorted.toList.Pairwise fun left right ↦ compare (key left) (key right) = .lt := by
  induction relation using inductionOn with
  | ofList rows =>
    change (sortedRows key rows).map List.toArray = some sorted at found
    cases listFound : sortedRows key rows with
    | none => simp [listFound] at found
    | some list =>
      simp only [listFound, Option.map_some, Option.some.injEq] at found
      subst found
      obtain ⟨same, ascending⟩ := sortedRows_some listFound
      exact ⟨fun row ↦ by simpa using same.mem_iff (a := row), by simpa using ascending⟩

/-- What `sortedBy?` returns is the relation's list, every row once, in an order. -/
theorem sortedBy?_ofList [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key]
    {key : Row → Key} {relation : Relation Row} {sorted : Array Row}
    (found : relation.sortedBy? key = some sorted) : ofList sorted.toList = relation := by
  induction relation using inductionOn with
  | ofList rows =>
    change (sortedRows key rows).map List.toArray = some sorted at found
    cases listFound : sortedRows key rows with
    | none => simp [listFound] at found
    | some list =>
      simp only [listFound, Option.map_some, Option.some.injEq] at found
      subst found
      exact sound (sortedRows_some listFound).1

/-- `sortedBy?` returns rows exactly when `key` is a key of the relation. -/
theorem sortedBy?_isSome [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key]
    {key : Row → Key} {relation : Relation Row} :
    (relation.sortedBy? key).isSome ↔ relation.Keyed key := by
  induction relation using inductionOn with
  | ofList rows =>
    change ((sortedRows key rows).map List.toArray).isSome ↔ _
    rw [Option.isSome_map]
    exact sortedRows_isSome (key := key)

/-- The rows in ascending order of `key`, given that it is a key of the relation (`keyed`): what
`sortedBy?` returns, which is rows exactly for a key (`sortedBy?_isSome`), with no `Option` left to
handle. -/
def sortedByKey [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key] (relation : Relation Row)
    (key : Row → Key) (keyed : relation.Keyed key) : Array Row :=
  (relation.sortedBy? key).get (sortedBy?_isSome.mpr keyed)

/-- `sortedByKey` lists what `sortedBy?` finds. -/
theorem sortedByKey_eq [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key] {relation : Relation Row}
    {key : Row → Key} {keyed : relation.Keyed key} {sorted : Array Row}
    (found : relation.sortedBy? key = some sorted) : relation.sortedByKey key keyed = sorted :=
  Option.get_of_mem _ found

/-- `sortedByKey` holds the relation's rows (`sortedBy?_eq_some`). -/
theorem mem_sortedByKey [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key] {relation : Relation Row}
    {key : Row → Key} {keyed : relation.Keyed key} {row : Row} :
    row ∈ relation.sortedByKey key keyed ↔ row ∈ relation :=
  (sortedBy?_eq_some (Option.some_get _).symm).1 row

/-! ### Reducing -/

/-- The images under `value` of every row, repetitions included, combined in `monoid` in a balanced
tree (`CommMonoid.combine`): n - 1 applications of `op`, O(n) work besides.  The monoid's
commutativity is what makes the result a function of the relation, which has no order to fold
in. -/
def reduce {M : Type} (monoid : CommMonoid M) (value : Row → M) (relation : Relation Row) : M :=
  Quotient.liftOn relation (fun rows ↦ monoid.combine (rows.map value)) fun left right same ↦ by
    simp only [CommMonoid.combine_eq_foldr]
    exact monoid.foldr_perm (same.map value)

theorem reduce_ofList {M : Type} {monoid : CommMonoid M} {value : Row → M} {rows : List Row} :
    (ofList rows).reduce monoid value = (rows.map value).foldr monoid.op monoid.unit :=
  monoid.combine_eq_foldr _

@[simp] theorem reduce_empty {M : Type} {monoid : CommMonoid M} {value : Row → M} :
    (∅ : Relation Row).reduce monoid value = monoid.unit :=
  reduce_ofList

theorem reduce_union {M : Type} {monoid : CommMonoid M} {value : Row → M} {left right : Relation Row} :
    (left ∪ right).reduce monoid value = monoid.op (left.reduce monoid value) (right.reduce monoid value) := by
  induction left using inductionOn with
  | ofList left =>
  induction right using inductionOn with
  | ofList right =>
    show (ofList (left ++ right)).reduce monoid value = _
    rw [reduce_ofList, reduce_ofList, reduce_ofList, List.map_append, monoid.foldr_append]

theorem reduce_project {M : Type} {monoid : CommMonoid M} {value : Result → M}
    {projection : Row → Result} {relation : Relation Row} :
    (relation.project projection).reduce monoid value = relation.reduce monoid (value ∘ projection) := by
  induction relation using inductionOn with
  | ofList rows =>
    show (ofList (rows.map projection)).reduce monoid value = _
    rw [reduce_ofList, reduce_ofList, List.map_map]

/-- The rows of a group are the relation's rows with its key. -/
theorem mem_of_mem_groupBy [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key] {key : Row → Key}
    {relation : Relation Row} {value : Key} {group : Relation Row}
    (found : (value, group) ∈ relation.groupBy key) {row : Row} :
    row ∈ group ↔ row ∈ relation ∧ key row = value := by
  obtain ⟨_, rfl⟩ := mem_groupBy.mp found
  rw [mem_select, beq_iff_eq]
  exact and_congr_right fun _ ↦
    ⟨Std.LawfulEqCmp.eq_of_compare, fun same ↦ same ▸ Std.ReflCmp.compare_self⟩

/-- Each key occurs in one group. -/
theorem groupBy_keyed {Key : Type} [Ord Key] [Std.TransOrd Key] [Std.LawfulEqOrd Key] {key : Row → Key}
    {relation : Relation Row} : (relation.groupBy key).Keyed Prod.fst := by
  induction relation using inductionOn with
  | ofList rows =>
    show Relational.Keyed (groups key rows) Prod.fst
    simp only [groups_eq, Relational.Keyed, List.map_map, Function.comp_def, List.map_id']
    exact nodup_toList (keySet key rows)

/-- A group of a relation keyed by `other` is keyed by it: its rows are some of the relation's. -/
theorem Keyed.group {K : Type} [TreeOrd Key] {key : Row → Key} {other : Row → K} {relation : Relation Row}
    {value : Key} {group : Relation Row} (keyed : relation.Keyed other)
    (found : (value, group) ∈ relation.groupBy key) : group.Keyed other := by
  obtain ⟨_, rfl⟩ := mem_groupBy.mp found
  exact keyed.select

/-- Relations under `union`, the empty one its unit. -/
@[expose] def unionMonoid : CommMonoid (Relation Row) where
  unit := ∅
  op := (· ∪ ·)
  assoc first second third := by
    induction first using inductionOn with
    | ofList first =>
    induction second using inductionOn with
    | ofList second =>
    induction third using inductionOn with
    | ofList third => exact sound (List.Perm.of_eq (List.append_assoc _ _ _))
  comm first second := by
    induction first using inductionOn with
    | ofList first =>
    induction second using inductionOn with
    | ofList second => exact sound List.perm_append_comm
  unit_op value := by
    induction value using inductionOn with
    | ofList rows => rfl

/-- The union of the relations that `expand` gives the rows, each row's as often as it occurs: the
relational bind.  A right fold of `union`, which appends lists, in O(N) time for the N rows of the
result: a balanced tree would copy each left half again at every level.  It is `reduce` in
`unionMonoid` (`bind_eq_reduce`). -/
@[expose] def bind {Result : Type} (expand : Row → Relation Result) (relation : Relation Row) :
    Relation Result :=
  Quotient.liftOn relation (fun rows ↦ (rows.map expand).foldr (· ∪ ·) ∅) fun _ _ same ↦
    unionMonoid.foldr_perm (same.map expand)

theorem bind_eq_reduce {Result : Type} {expand : Row → Relation Result} {relation : Relation Row} :
    relation.bind expand = relation.reduce unionMonoid expand := by
  induction relation using inductionOn with
  | ofList rows =>
    rw [reduce_ofList]
    rfl

/-- How often a row occurs in a bind: the sum over the rows of how often it occurs in what each
gives. -/
theorem multiplicity_bind {Result : Type} [DecidableEq Result] {expand : Row → Relation Result}
    {relation : Relation Row} {result : Result} :
    (relation.bind expand).multiplicity result =
      relation.reduce .nat fun row ↦ (expand row).multiplicity result := by
  induction relation using inductionOn with
  | ofList rows =>
    rw [reduce_ofList]
    show ((rows.map expand).foldr (· ∪ ·) ∅).multiplicity result = _
    induction rows with
    | nil => rfl
    | cons head rest ih =>
      simp only [List.map_cons, List.foldr_cons, multiplicity_union, ih]
      rfl

@[simp] theorem mem_bind {Result : Type} {expand : Row → Relation Result} {relation : Relation Row}
    {result : Result} : result ∈ relation.bind expand ↔ ∃ row ∈ relation, result ∈ expand row := by
  induction relation using inductionOn with
  | ofList rows =>
    show result ∈ (rows.map expand).foldr (· ∪ ·) ∅ ↔ _
    induction rows with
    | nil => simp
    | cons head rest ih =>
      simp only [List.map_cons, List.foldr_cons] at ih ⊢
      show result ∈ expand head ∪ _ ↔ _
      rw [mem_union, ih]
      simp

/-- Grouping rows by keys that are distinct and cover them, and putting the groups together, gives
the rows again, in another order. -/
private theorem flatMap_groups_perm {Key : Type} [TreeOrd Key]
    {key : Row → Key} {keys : List Key} {rows : List Row} (distinct : keys.Nodup)
    (covers : ∀ row ∈ rows, key row ∈ keys) :
    (keys.flatMap fun value ↦ rows.filter fun row ↦ TreeOrd.cmp (key row) value == .eq).Perm rows := by
  classical
  rw [List.perm_iff_count]
  intro row
  rw [List.count_flatMap]
  have term : ∀ value, (List.count row ∘ fun value ↦
      rows.filter fun other ↦ TreeOrd.cmp (key other) value == .eq) value =
        if key row = value then rows.count row else 0 := by
    intro value
    simp only [Function.comp]
    by_cases same : key row = value
    · rw [ite_eq_left same, List.count_filter (by simp [same, Std.ReflCmp.compare_self])]
    · rw [ite_eq_right same, List.count_eq_zero_of_not_mem]
      simp only [List.mem_filter, beq_iff_eq, not_and]
      intro _ equal
      exact same (Std.LawfulEqCmp.eq_of_compare equal)
  rw [List.map_congr_left fun value _ ↦ term value]
  have sum : ∀ values : List Key, values.Nodup →
      (values.map fun value ↦ if key row = value then rows.count row else 0).sum =
        if key row ∈ values then rows.count row else 0 := by
    intro values fresh
    induction values with
    | nil => simp
    | cons head rest ih =>
      obtain ⟨absent, rest'⟩ := List.nodup_cons.mp fresh
      simp only [List.map_cons, List.sum_cons, ih rest', List.mem_cons]
      by_cases same : key row = head
      · subst same
        simp [absent]
      · simp [same]
  rw [sum keys distinct]
  by_cases member : row ∈ rows
  · simp [covers row member]
  · simp [List.count_eq_zero_of_not_mem member]

/-- The groups put together are the relation again: grouping loses no row and repeats none. -/
theorem bind_groupBy {Key : Type} [TreeOrd Key]
    {key : Row → Key} {relation : Relation Row} : (relation.groupBy key).bind Prod.snd = relation := by
  induction relation using inductionOn with
  | ofList rows =>
    show ((groups key rows).map Prod.snd).foldr (· ∪ ·) ∅ = ofList rows
    rw [groups_eq]
    have flat : ∀ values : List Key,
        ((values.map fun value ↦
          (value, ofList (rows.filter fun row ↦ TreeOrd.cmp (key row) value == .eq))).map Prod.snd).foldr
            (· ∪ ·) ∅ =
          ofList (values.flatMap fun value ↦ rows.filter fun row ↦ TreeOrd.cmp (key row) value == .eq) := by
      intro values
      induction values with
      | nil => rfl
      | cons head rest ih =>
        simp only [List.map_cons, List.foldr_cons, ih, List.flatMap_cons]
        rfl
    rw [flat]
    apply sound
    apply flatMap_groups_perm (nodup_toList _)
    intro row member
    rw [Std.ExtTreeSet.mem_toList, mem_keySet]
    exact ⟨row, member, rfl⟩

/-- Each key that some row has, with `monoid`'s reduction of the values of the rows that have
it: a sum, count or maximum per key, in O(n log n) time for n rows and the reductions. -/
def aggregateBy {M Key : Type} [TreeOrd Key] (key : Row → Key)
    (monoid : CommMonoid M) (value : Row → M) (relation : Relation Row) : Relation (Key × M) :=
  (relation.groupBy key).project fun (group, rows) ↦ (group, rows.reduce monoid value)

@[simp] theorem mem_aggregateBy {M Key : Type} [TreeOrd Key]
    {key : Row → Key} {monoid : CommMonoid M} {value : Row → M} {relation : Relation Row}
    {group : Key} {result : M} :
    (group, result) ∈ relation.aggregateBy key monoid value ↔ (∃ row ∈ relation, key row = group) ∧
      result = (relation.select fun row ↦ TreeOrd.cmp (key row) group == .eq).reduce monoid value := by
  simp only [aggregateBy, mem_project, Prod.exists, Prod.mk.injEq, mem_groupBy]
  constructor
  · rintro ⟨_, _, ⟨found, rfl⟩, rfl, rfl⟩
    exact ⟨found, rfl⟩
  · rintro ⟨found, rfl⟩
    exact ⟨group, _, ⟨found, rfl⟩, rfl, rfl⟩

/-- A relation's number of rows is its sum of ones. -/
theorem count_eq_reduce {relation : Relation Row} : relation.count = relation.reduce .nat fun _ ↦ 1 := by
  induction relation using inductionOn with
  | ofList rows =>
    rw [reduce_ofList, count_ofList]
    induction rows with
    | nil => rfl
    | cons head rest ih =>
      simp only [List.length_cons, List.map_cons, List.foldr_cons, ih]
      show _ = 1 + _
      omega

/-! ### Reachability -/

section Reach

variable {Node : Type}

/-- The nodes reachable from `seeds` along `edges`: the seeds, and every node an edge leads to from a
reachable node. -/
inductive Reaches (edges : Relation (Node × Node)) (seeds : Relation Node) : Node → Prop
  | seed {node : Node} : node ∈ seeds → Reaches edges seeds node
  | step {source target : Node} : Reaches edges seeds source → (source, target) ∈ edges →
      Reaches edges seeds target

variable [TreeOrd Node]

/-- A node is in a tree with another inserted if it is the other or was in the tree. -/
private theorem mem_insert_iff {nodes : Std.ExtTreeSet Node TreeOrd.cmp} {node added : Node} :
    node ∈ nodes.insert added ↔ node = added ∨ node ∈ nodes := by
  rw [Std.ExtTreeSet.mem_insert]
  exact or_congr_left ⟨fun same ↦ (Std.LawfulEqCmp.eq_of_compare same).symm,
    fun same ↦ same ▸ Std.ReflCmp.compare_self⟩

/-- Each node of `candidates` that `reached` lacks, inserted into `reached` and put in front of
`added`, once: a step's new nodes, and the tree of the nodes reached with them. -/
private def admit : Std.ExtTreeSet Node TreeOrd.cmp → List Node → List Node →
    Std.ExtTreeSet Node TreeOrd.cmp × List Node
  | reached, added, [] => (reached, added)
  | reached, added, candidate :: rest =>
    if reached.contains candidate then admit reached added rest
    else admit (reached.insert candidate) (candidate :: added) rest

/-- `admit` reaches every candidate, adds those `reached` lacked, and grows by as many nodes as it
adds. -/
private theorem admit_spec : ∀ (reached : Std.ExtTreeSet Node TreeOrd.cmp) (added candidates : List Node),
    (∀ node, node ∈ (admit reached added candidates).1 ↔ node ∈ reached ∨ node ∈ candidates) ∧
      (∀ node, node ∈ (admit reached added candidates).2 ↔
        node ∈ added ∨ node ∈ candidates ∧ node ∉ reached) ∧
      (admit reached added candidates).1.size + added.length =
        reached.size + (admit reached added candidates).2.length
  | reached, added, [] => by simp [admit]
  | reached, added, candidate :: rest => by
    by_cases present : reached.contains candidate
    · obtain ⟨members, news, size⟩ := admit_spec reached added rest
      have old : candidate ∈ reached := Std.ExtTreeSet.mem_iff_contains.mpr present
      simp only [admit, present, ↓reduceIte]
      refine ⟨fun node ↦ ?_, fun node ↦ ?_, size⟩
      · by_cases same : node = candidate <;> simp [members, same, old]
      · by_cases same : node = candidate <;> simp [news, same, old]
    · obtain ⟨members, news, size⟩ := admit_spec (reached.insert candidate) (candidate :: added) rest
      have absent : candidate ∉ reached := fun member ↦
        present (Std.ExtTreeSet.mem_iff_contains.mp member)
      simp only [admit, present, Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun node ↦ ?_, fun node ↦ ?_, ?_⟩
      · by_cases same : candidate = node
        · subst same
          simp [members]
        · simp [members, same, Ne.symm same]
      · by_cases same : candidate = node
        · subst same
          simp [news, absent]
        · simp [news, same, Ne.symm same]
      · simp only [List.length_cons, Std.ExtTreeSet.size_insert, present, Bool.false_eq_true,
          ↓reduceIte] at size
        omega

/-- The targets of the edges out of the nodes of `frontier`, looked up in `successors`, which files
the edges under their sources. -/
private def targetsOf (successors : Std.ExtTreeMap Node (List (Node × Node)) TreeOrd.cmp)
    (frontier : List Node) : List Node :=
  frontier.flatMap fun node ↦ (successors.getD node []).map Prod.snd

/-- What `successors` must be for the walk along `edges`: each edge filed under its source. -/
private abbrev Files (successors : Std.ExtTreeMap Node (List (Node × Node)) TreeOrd.cmp)
    (edges : List (Node × Node)) : Prop :=
  ∀ source edge, edge ∈ successors.getD source [] ↔ edge ∈ edges ∧ edge.1 = source

/-- A step from `frontier`: the nodes reached after it are those reached before and the targets of
the edges out of the frontier; the nodes it adds are the targets that were not reached; and the tree
grows by as many nodes as the step adds. -/
private theorem admit_step {edges : List (Node × Node)}
    {successors : Std.ExtTreeMap Node (List (Node × Node)) TreeOrd.cmp} (filed : Files successors edges)
    {reached next : Std.ExtTreeSet Node TreeOrd.cmp} {frontier added : List Node}
    (step : admit reached [] (targetsOf successors frontier) = (next, added)) :
    (∀ node, node ∈ next ↔ node ∈ reached ∨ ∃ source ∈ frontier, (source, node) ∈ edges) ∧
      (∀ node, node ∈ added ↔ (∃ source ∈ frontier, (source, node) ∈ edges) ∧ node ∉ reached) ∧
      next.size = reached.size + added.length := by
  have targets : ∀ node, node ∈ targetsOf successors frontier ↔
      ∃ source ∈ frontier, (source, node) ∈ edges := fun node ↦ by
    simp only [targetsOf, List.mem_flatMap, List.mem_map, filed]
    constructor
    · rintro ⟨source, member, ⟨other, target⟩, ⟨edge, rfl⟩, rfl⟩
      exact ⟨other, member, edge⟩
    · rintro ⟨source, member, edge⟩
      exact ⟨source, member, (source, node), ⟨edge, rfl⟩, rfl⟩
  obtain ⟨members, news, size⟩ := admit_spec reached [] (targetsOf successors frontier)
  rw [step] at members news size
  simp only [List.not_mem_nil, false_or, List.length_nil, Nat.add_zero, targets] at members news size
  exact ⟨members, news, size⟩

/-- A tree whose nodes are all seeds or targets of edges has at most as many nodes as the lists
have entries. -/
private theorem size_le_of_candidate {edges : List (Node × Node)} {seeds : List Node}
    {reached : Std.ExtTreeSet Node TreeOrd.cmp}
    (candidate : ∀ node ∈ reached, node ∈ seeds ∨ ∃ source, (source, node) ∈ edges) :
    reached.size ≤ seeds.length + edges.length := by
  have length : (seeds ++ edges.map Prod.snd).length = seeds.length + edges.length := by simp
  rw [← length, ← Std.ExtTreeSet.length_toList]
  apply (nodup_toList reached).length_le_of_subset
  intro node member
  rcases candidate node (Std.ExtTreeSet.mem_toList.mp member) with seed | ⟨source, edge⟩
  · exact List.mem_append_left _ seed
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨(source, node), edge, rfl⟩)

/-- After a step, the nodes reached are still seeds or targets of edges. -/
private theorem candidate_step {edges : List (Node × Node)} {seeds : List Node}
    {successors : Std.ExtTreeMap Node (List (Node × Node)) TreeOrd.cmp} (filed : Files successors edges)
    {reached next : Std.ExtTreeSet Node TreeOrd.cmp} {frontier added : List Node}
    (candidate : ∀ node ∈ reached, node ∈ seeds ∨ ∃ source, (source, node) ∈ edges)
    (step : admit reached [] (targetsOf successors frontier) = (next, added)) :
    ∀ node ∈ next, node ∈ seeds ∨ ∃ source, (source, node) ∈ edges := by
  intro node member
  rcases ((admit_step filed step).1 node).mp member with old | ⟨source, _, edge⟩
  · exact candidate node old
  · exact Or.inr ⟨source, edge⟩

/-- A step that adds a node leaves fewer seeds and targets of edges unreached: what ends `spread`. -/
private theorem shrinks_step {edges : List (Node × Node)} {seeds : List Node}
    {successors : Std.ExtTreeMap Node (List (Node × Node)) TreeOrd.cmp} (filed : Files successors edges)
    {reached next : Std.ExtTreeSet Node TreeOrd.cmp} {frontier : List Node} {first : Node}
    {rest : List Node} (candidate : ∀ node ∈ reached, node ∈ seeds ∨ ∃ source, (source, node) ∈ edges)
    (step : admit reached [] (targetsOf successors frontier) = (next, first :: rest)) :
    seeds.length + edges.length - next.size < seeds.length + edges.length - reached.size := by
  have bound := size_le_of_candidate (candidate_step filed candidate step)
  have size := (admit_step filed step).2.2
  simp only [List.length_cons] at size
  omega

/-- Semi-naive steps: the targets of the edges out of `frontier`, the nodes the last step added, go
into `reached`, and those it lacked are the next frontier, until a step adds no node.  It ends
because every step that goes on adds a node to `reached`, and the nodes reached are all seeds or
targets of edges (`candidate`), finitely many. -/
private def spread {edges : List (Node × Node)} {seeds : List Node}
    (successors : Std.ExtTreeMap Node (List (Node × Node)) TreeOrd.cmp) (filed : Files successors edges)
    (reached : Std.ExtTreeSet Node TreeOrd.cmp)
    (candidate : ∀ node ∈ reached, node ∈ seeds ∨ ∃ source, (source, node) ∈ edges)
    (frontier : List Node) : Std.ExtTreeSet Node TreeOrd.cmp :=
  match step : admit reached [] (targetsOf successors frontier) with
  | (next, []) => next
  | (next, first :: rest) =>
    spread successors filed next (candidate_step filed candidate step) (first :: rest)
termination_by seeds.length + edges.length - reached.size
decreasing_by exact shrinks_step filed candidate step

/-- What `spread` keeps true from step to step: every node reached is reachable, the seeds are
reached, the frontier is reached, and every edge out of a reached node outside the frontier leads to
a reached node.  When a step adds no node, the frontier's edges lead to reached nodes as well, so the
nodes reached are closed under the edges and hold every reachable node. -/
private theorem spread_spec {edges : List (Node × Node)} {seeds : List Node}
    {successors : Std.ExtTreeMap Node (List (Node × Node)) TreeOrd.cmp} (filed : Files successors edges)
    (reached : Std.ExtTreeSet Node TreeOrd.cmp)
    (candidate : ∀ node ∈ reached, node ∈ seeds ∨ ∃ source, (source, node) ∈ edges)
    (frontier : List Node)
    (sound : ∀ node ∈ reached, Reaches (ofList edges) (ofList seeds) node)
    (seeded : ∀ node ∈ seeds, node ∈ reached)
    (inside : ∀ node ∈ frontier, node ∈ reached)
    (closed : ∀ source ∈ reached, source ∉ frontier → ∀ target, (source, target) ∈ edges →
      target ∈ reached) (node : Node) :
    node ∈ spread successors filed reached candidate frontier ↔
      Reaches (ofList edges) (ofList seeds) node := by
  unfold spread
  split
  · rename_i next step
    obtain ⟨members, news, _⟩ := admit_step filed step
    refine ⟨fun member ↦ ?_, fun reaches ↦ (members node).mpr (Or.inl ?_)⟩
    · rcases (members node).mp member with old | ⟨source, member, edge⟩
      · exact sound node old
      · exact Reaches.step (sound source (inside source member)) (mem_ofList.mpr edge)
    · induction reaches with
      | seed member => exact seeded _ member
      | @step source target _ edge previous =>
        by_cases fromFrontier : source ∈ frontier
        · exact Classical.byContradiction fun absent ↦
            List.not_mem_nil ((news target).mpr ⟨⟨source, fromFrontier, edge⟩, absent⟩)
        · exact closed source previous fromFrontier target edge
  · rename_i next first rest step
    obtain ⟨members, news, _⟩ := admit_step filed step
    have := shrinks_step filed candidate step
    apply spread_spec filed next _ (first :: rest)
    · intro node member
      rcases (members node).mp member with old | ⟨source, member, edge⟩
      · exact sound node old
      · exact Reaches.step (sound source (inside source member)) (mem_ofList.mpr edge)
    · exact fun node member ↦ (members node).mpr (Or.inl (seeded node member))
    · exact fun node member ↦ (members node).mpr (Or.inr ((news node).mp member).1)
    · intro source member notAdded target edge
      apply (members target).mpr
      have old : source ∈ reached := by
        rcases (members source).mp member with old | fromFrontier
        · exact old
        · exact Classical.byContradiction fun absent ↦
            notAdded ((news source).mpr ⟨fromFrontier, absent⟩)
      by_cases fromFrontier : source ∈ frontier
      · exact Or.inr ⟨source, fromFrontier, edge⟩
      · exact Or.inl (closed source old fromFrontier target edge)
termination_by seeds.length + edges.length - reached.size
decreasing_by omega

/-- The nodes reachable from `seeds` along `edges`, through a tree of the edges by source. -/
private def reachSet (edges : List (Node × Node)) (seeds : List Node) : Std.ExtTreeSet Node TreeOrd.cmp :=
  spread (grouped Prod.fst edges) (fun _ _ ↦ mem_grouped) (keySet id seeds)
    (fun node member ↦ Or.inl (by simpa [mem_keySet] using member)) (keySet id seeds).toList

private theorem mem_reachSet {edges : List (Node × Node)} {seeds : List Node} {node : Node} :
    node ∈ reachSet edges seeds ↔ Reaches (ofList edges) (ofList seeds) node := by
  have start : ∀ node, node ∈ keySet id seeds ↔ node ∈ seeds := fun _ ↦ by simp [mem_keySet]
  exact spread_spec _ _ _ _ (fun node member ↦ Reaches.seed (mem_ofList.mpr ((start node).mp member)))
    (fun node member ↦ (start node).mpr member) (fun _ member ↦ Std.ExtTreeSet.mem_toList.mp member)
    (fun _ member outside ↦ absurd (Std.ExtTreeSet.mem_toList.mpr member) outside) node

/-- The nodes reachable from `seeds` along `edges` (`mem_reach`), each once (`reach_keyed`), by
semi-naive evaluation, as Datalog engines evaluate a recursive rule: the seeds, and then at each step
the targets of the edges out of the frontier alone, the nodes the step before added, until a step
adds no node.  The edges are filed under their sources in a tree once, and each node is in the
frontier of one step only, so every edge is looked at once, when its source joins the frontier, and
its target is looked up in a tree of the nodes reached: O((k + m) log (k + m)) time in all, for k
seeds and m edges, whatever the distance of the nodes from the seeds.  How often a seed or an edge
repeats changes nothing. -/
def reach (edges : Relation (Node × Node)) (seeds : Relation Node) : Relation Node :=
  lift2 (fun edges seeds ↦ (reachSet edges seeds).toList)
    (fun edges edges' seeds seeds' sameEdges sameSeeds ↦ List.Perm.of_eq
      (congrArg (fun nodes ↦ Std.ExtTreeSet.toList nodes) (Std.ExtTreeSet.ext_mem fun node ↦ by
        rw [mem_reachSet, mem_reachSet, sound sameEdges, sound sameSeeds])))
    edges seeds

@[simp] theorem mem_reach {edges : Relation (Node × Node)} {seeds : Relation Node} {node : Node} :
    node ∈ reach edges seeds ↔ Reaches edges seeds node := by
  induction edges using inductionOn with
  | ofList edges =>
  induction seeds using inductionOn with
  | ofList seeds =>
    show node ∈ (reachSet edges seeds).toList ↔ _
    rw [Std.ExtTreeSet.mem_toList, mem_reachSet]

theorem reach_keyed {edges : Relation (Node × Node)} {seeds : Relation Node} :
    (reach edges seeds).Keyed id := by
  induction edges using inductionOn with
  | ofList edges =>
  induction seeds using inductionOn with
  | ofList seeds =>
    show Relational.Keyed (reachSet edges seeds).toList id
    simpa [Relational.Keyed] using nodup_toList (reachSet edges seeds)

end Reach

/-! A relation maps its rows as a field of a record family does (`deriving MapM`): purely by
`project`, and in a monad whose effects commute (`DeriveMapM.CommutativeMonad`, such as `Option`), row
by row, the rows' order, which a relation does not have, not changing the result
(`DeriveMapM.mapM_perm`).  So a family's field of type `Relation (ρ × V)` maps its references from ids
to keys and back as an array of them would, but in `Option` only: the family derives `MapC`, not
`MapM`. -/

instance : DeriveMapM.MapC Relation where
  map := project
  mapC g := Quotient.lift (fun rows ↦ ofList <$> rows.mapM g) fun _ _ same ↦ DeriveMapM.mapM_perm g same

-- the references of a bag map in `Option`, failing if one does not map, whatever the rows' order
#guard (DeriveMapM.MapC.mapC (fun n : Nat ↦ if n < 5 then some (n + 1) else none) (ofList [3, 1, 2])) ==
  some (ofList [2, 3, 4])
#guard (DeriveMapM.MapC.mapC (fun n : Nat ↦ if n < 3 then some n else none) (ofList [3, 1, 2])).isNone

end Relation

end Relational
