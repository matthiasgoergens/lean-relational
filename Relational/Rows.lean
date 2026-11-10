module

public import Std.Data.ExtTreeMap
public import Std.Data.ExtTreeSet
public import Relational.Relation
public import Relational.TreeOrd
public import Std.Data.HashMap
-- `included_iff` unfolds core's `withPtrEq`, whose body Init does not expose
import all Init.Util
-- the search lemmas of the trees behind `Std.ExtTreeMap` (`Rows.under`)
import Std.Data.DTreeMap.Internal.Lemmas


public section

namespace Relational

/-! The rows of one table, held in a persistent balanced tree from the primary key to the row.
Inserting a row copies one path of the tree and shares the rest, so a database that keeps its
earlier versions pays little for them, and the primary key is unique by construction.  The tree
is an extensional one (`Std.ExtTreeMap`, a quotient of the trees by their entries), so two
tables with the same rows are equal and nothing, not even the recursor of `Rows`, can see the
shape that the order of insertion gave the tree.  Queries see the rows as a `Relation`; `keys`,
`toList`, `maxKey?`, `above` and `first?` read the key order, which is the order of a column, and so
only for a key whose order means something, one with an `Ord`; a record's or a relation's key has
only the order the tree keeps it in (`TreeOrd`), and `any?`, `keysInAnyOrder` and
`toListInAnyOrder` read any table.  An `Index` maps the values of a column to the primary keys of
the rows that have them. -/

namespace CompositeKeys

/-! Lexicographic order on pairs, for a sort by a pair of columns: `open scoped
Relational.CompositeKeys` where one is sorted by.  Not a global instance, since pairs have no one
canonical order.  Trees over pairs need none of it: they keep pairs in the lexicographic order of
their components' tree orders (`TreeOrd.prod`). -/

attribute [scoped instance] lexOrd

end CompositeKeys

section
open scoped CompositeKeys
-- With the lexicographic `Ord` in scope, pairs still have the one tree order, which agrees with it.
example : (inferInstance : TreeOrd (Nat × Nat)) = TreeOrd.prod := rfl
example : TreeOrd.Agrees (Nat × Nat) := inferInstance
end

/-- The rows of a table whose primary key is `key`. -/
structure Rows {Row Key : Type} [TreeOrd Key] (key : Row → Key) where
  private mk ::
  private tree : Std.ExtTreeMap Key Row TreeOrd.cmp
  private keyed : ∀ primary row, tree[primary]? = some row → key row = primary

namespace Rows

variable {Row Key : Type} [TreeOrd Key] {key : Row → Key}

/-- The table without rows. -/
def empty : Rows key := ⟨∅, fun _ _ found ↦ by simp at found⟩

instance : EmptyCollection (Rows key) := ⟨empty⟩

/-- The row with primary key `primary`. -/
def find? (rows : Rows key) (primary : Key) : Option Row := rows.tree[primary]?

-- membership through `find?`, since an instance's body is exposed and the tree is a private field
instance : Membership Row (Rows key) := ⟨fun rows row ↦ rows.find? (key row) = some row⟩

instance [DecidableEq Row] (row : Row) (rows : Rows key) : Decidable (row ∈ rows) :=
  inferInstanceAs (Decidable (rows.find? (key row) = some row))

/-- Whether some row has primary key `primary`. -/
def contains (rows : Rows key) (primary : Key) : Bool := rows.tree.contains primary

/-- The number of rows. -/
def count (rows : Rows key) : Nat := rows.tree.size

/-- The rows as a relation, for queries. -/
def toRelation (rows : Rows key) : Relation Row := Relation.ofList (rows.tree.toList.map Prod.snd)

/-- The rows, in an order that is not said (`keysInAnyOrder`): for a fold whose result no order
changes. -/
def toListInAnyOrder (rows : Rows key) : List Row := rows.tree.toList.map Prod.snd

/-- The rows, in the order of their primary keys. -/
def toList [Ord Key] [TreeOrd.Agrees Key] (rows : Rows key) : List Row := rows.toListInAnyOrder

/-- The primary keys, in an order that is not said.  For generic code over every table and for
code that reads them as a set; `keys` lists them in order where the order means something. -/
def keysInAnyOrder (rows : Rows key) : List Key := rows.tree.keys

/-- The rows of each group, `group` giving each row's, in ascending order of `order` within a
group, as the items of a list column are read for each record: a key whose own order means nothing
(a record's) groups them, and a column whose order means something (a position) orders them; rows
that tie on it come in an order not said.  One pass and a merge sort of each group (`List.mergeSort`,
whose order the row read-back laws use), in O(n log n) time for n rows. -/
def groupedBy {Group Order : Type} [BEq Group] [Hashable Group] [Ord Order]
    (rows : Rows key) (group : Row → Group) (order : Row → Order) : Std.HashMap Group (Array Row) :=
  (rows.toListInAnyOrder.foldl (init := ({} : Std.HashMap Group (Array Row))) fun groups row ↦
    groups.insert (group row) ((groups.getD (group row) #[]).push row)).map fun _ members ↦
      (members.toList.mergeSort fun left right ↦ (compare (order left) (order right)).isLE).toArray

/-- The primary keys, in ascending order: the tree's, which is `compare`'s (`TreeOrd.Agrees`). -/
def keys [Ord Key] [TreeOrd.Agrees Key] (rows : Rows key) : List Key := rows.keysInAnyOrder

/-- The greatest primary key, as the next free sequence number or timestamp is computed: in
O(log n) time for n rows. -/
def maxKey? [Ord Key] [TreeOrd.Agrees Key] (rows : Rows key) : Option Key := rows.tree.maxKey?

private theorem keyed_insert {tree : Std.ExtTreeMap Key Row TreeOrd.cmp}
    (keyed : ∀ primary row, tree[primary]? = some row → key row = primary) (row : Row) :
    ∀ primary other, (tree.insert (key row) row)[primary]? = some other → key other = primary :=
  fun primary other found ↦ by
    rw [Std.ExtTreeMap.getElem?_insert] at found
    split at found
    · rename_i same
      cases found
      exact Std.LawfulEqCmp.eq_of_compare same
    · exact keyed primary other found

/-- The table with `row` added if no row has its primary key, and unchanged otherwise. -/
def insertIfNew (rows : Rows key) (row : Row) : Rows key :=
  if rows.tree.contains (key row) then rows
  else ⟨rows.tree.insert (key row) row, keyed_insert rows.keyed row⟩

/-- The table with `row` added, or `none` if a row has its primary key: `insertIfNew` when that adds
the row, in one lookup of the key fewer than asking `contains` first. -/
def insertNew? (rows : Rows key) (row : Row) : Option (Rows key) :=
  if rows.tree.contains (key row) then none
  else some ⟨rows.tree.insert (key row) row, keyed_insert rows.keyed row⟩

theorem insertNew?_eq (rows : Rows key) (row : Row) :
    rows.insertNew? row = if rows.contains (key row) then none else some (rows.insertIfNew row) := by
  simp only [insertNew?, contains, insertIfNew]
  split <;> rfl

/-- The table with `row` added, unchanged if it already has `row`, or `none` if a different row
has its primary key. -/
def insert? [DecidableEq Row] (rows : Rows key) (row : Row) : Option (Rows key) :=
  match rows.find? (key row) with
  | some existing => if existing = row then some rows else none
  | none => some (rows.insertIfNew row)

/-- The table with the rows of `rows` added, or the first row whose primary key a different row
has. -/
def insertAll? [DecidableEq Row] (rows : Rows key) : List Row → Except Row (Rows key)
  | [] => .ok rows
  | row :: rest =>
    match rows.insert? row with
    | none => .error row
    | some next => next.insertAll? rest

/-- The table with exactly the rows of `rows`, or the first row whose primary key a different
row has. -/
def ofList? [DecidableEq Row] (rows : List Row) : Except Row (Rows key) :=
  (empty : Rows key).insertAll? rows

/-- The rows whose primary key is greater than `low`, as a table: each found from the one before
by a search of the tree, in O(d log n) time for d such rows of n, as the events a log holds after
a time are read. -/
def above [Ord Key] [TreeOrd.Agrees Key] (rows : Rows key) (low : Key) : Rows key :=
  go low rows.count empty
where
  /-- The rows after `primary`, at most `fuel` of them, added to `found`. -/
  go (primary : Key) : Nat → Rows key → Rows key
    | 0, found => found
    | fuel + 1, found =>
      match rows.tree.getEntryGT? primary with
      | some (next, row) => go next fuel (found.insertIfNew row)
      | none => found

theorem mem_iff {rows : Rows key} {row : Row} : row ∈ rows ↔ rows.find? (key row) = some row :=
  Iff.rfl

@[simp] theorem not_mem_empty {row : Row} : row ∉ (∅ : Rows key) := by
  intro member
  have : (∅ : Std.ExtTreeMap Key Row TreeOrd.cmp)[key row]? = some row := member
  simp at this

theorem find?_eq_some {rows : Rows key} {primary : Key} {row : Row} :
    rows.find? primary = some row ↔ row ∈ rows ∧ key row = primary := by
  constructor
  · intro found
    have same := rows.keyed primary row found
    subst same
    exact ⟨found, rfl⟩
  · rintro ⟨member, rfl⟩
    exact member

theorem contains_iff {rows : Rows key} {primary : Key} :
    rows.contains primary = true ↔ ∃ row ∈ rows, key row = primary := by
  simp only [contains, Std.ExtTreeMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists]
  constructor
  · rintro ⟨row, found⟩
    exact ⟨row, find?_eq_some.mp found⟩
  · rintro ⟨row, found⟩
    exact ⟨row, find?_eq_some.mpr found⟩

/-- Rows of a table that share the primary key are the same row. -/
theorem key_injective {rows : Rows key} {left right : Row} (leftMember : left ∈ rows)
    (rightMember : right ∈ rows) (same : key left = key right) : left = right := by
  have : rows.find? (key left) = some right := find?_eq_some.mpr ⟨rightMember, same.symm⟩
  rw [mem_iff.mp leftMember] at this
  exact Option.some.inj this

@[simp] theorem mem_toRelation {rows : Rows key} {row : Row} :
    row ∈ rows.toRelation ↔ row ∈ rows := by
  simp only [toRelation, Relation.mem_ofList, List.mem_map]
  constructor
  · rintro ⟨⟨primary, row⟩, member, rfl⟩
    have found := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp member
    exact (find?_eq_some.mp found).1
  · intro member
    exact ⟨(key row, row), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr member, rfl⟩

theorem mem_toListInAnyOrder {rows : Rows key} {row : Row} : row ∈ rows.toListInAnyOrder ↔ row ∈ rows := by
  have same := mem_toRelation (rows := rows) (row := row)
  simp only [toRelation, Relation.mem_ofList] at same
  exact same

/-- Folding rows into groups, as `groupedBy` does, adds to what `init` held of the group `k` the
rows of that group, in the order folded. -/
theorem groupFold_getD {Group : Type} [BEq Group] [Hashable Group] [LawfulBEq Group] (group : Row → Group)
    (k : Group) : ∀ (rows : List Row) (init : Std.HashMap Group (Array Row)),
      (rows.foldl (fun groups row ↦ groups.insert (group row) ((groups.getD (group row) #[]).push row))
          init).getD k #[] =
        init.getD k #[] ++ (rows.filter fun row ↦ group row == k).toArray
  | [], init => by simp
  | row :: rest, init => by
    rw [List.foldl_cons, groupFold_getD group k rest, Std.HashMap.getD_insert]
    by_cases same : group row = k
    · subst same
      simp
    · have : (group row == k) = false := by simpa using same
      simp [this]

/-- A group of `groupedBy`: its rows in ascending order of `order`, by a merge sort. -/
theorem groupedBy_getD {Group Order : Type} [BEq Group] [Hashable Group] [LawfulBEq Group] [Ord Order]
    (rows : Rows key) (group : Row → Group) (order : Row → Order) (k : Group) :
    (rows.groupedBy group order).getD k #[] =
      ((rows.toListInAnyOrder.filter fun row ↦ group row == k).mergeSort fun left right ↦
        (compare (order left) (order right)).isLE).toArray := by
  have grouped := groupFold_getD group k rows.toListInAnyOrder {}
  simp only [Std.HashMap.getD_empty, Array.empty_append] at grouped
  unfold groupedBy
  rw [Std.HashMap.getD_map]
  rw [Std.HashMap.getD_eq_getD_getElem?] at grouped
  generalize (rows.toListInAnyOrder.foldl _ _ : Std.HashMap Group (Array Row)) = folded at grouped ⊢
  cases found : folded[k]? with
  | none =>
    simp only [found, Option.getD_none] at grouped
    have empty : (rows.toListInAnyOrder.filter fun row ↦ group row == k) = [] := by
      simpa using grouped.symm
    simp [empty]
  | some members =>
    simp only [found, Option.getD_some] at grouped
    simp [grouped]

/-- A group of `groupedBy` holds exactly the rows of the table in that group. -/
theorem mem_groupedBy_getD {Group Order : Type} [BEq Group] [Hashable Group] [LawfulBEq Group] [Ord Order]
    {rows : Rows key} {group : Row → Group} {order : Row → Order} {k : Group} {row : Row} :
    row ∈ (rows.groupedBy group order).getD k #[] ↔ row ∈ rows ∧ group row = k := by
  rw [groupedBy_getD, List.mem_toArray, List.mem_mergeSort, List.mem_filter, mem_toListInAnyOrder, beq_iff_eq]

/-- A group of `groupedBy` keeps a key the table's rows do not share unshared. -/
theorem groupedBy_keyed {Group Order K : Type} [BEq Group] [Hashable Group] [LawfulBEq Group] [Ord Order]
    {rows : Rows key} {group : Row → Group} {order : Row → Order} {other : Row → K}
    (keyed : rows.toRelation.Keyed other) (k : Group) :
    (Relation.ofList ((rows.groupedBy group order).getD k #[]).toList).Keyed other := by
  rw [groupedBy_getD, List.toList_toArray]
  exact ((List.mergeSort_perm _ _).map other).nodup_iff.mpr ((List.filter_sublist.map other).nodup keyed)

/-- Tables with the same rows are equal: the shape of the tree, which depends on the order the
rows were inserted in, is not part of the value. -/
theorem ext {left right : Rows key} (same : ∀ row, row ∈ left ↔ row ∈ right) : left = right := by
  have trees : left.tree = right.tree := by
    apply Std.ExtTreeMap.ext_getElem?
    intro primary
    cases leftFound : left.tree[primary]? with
    | some row =>
      obtain ⟨member, rfl⟩ := find?_eq_some.mp leftFound
      exact ((same row).mp member).symm
    | none =>
      cases rightFound : right.tree[primary]? with
      | none => rfl
      | some row =>
        obtain ⟨member, rfl⟩ := find?_eq_some.mp rightFound
        have : left.tree[key row]? = some row := (same row).mpr member
        rw [leftFound] at this
        cases this
  cases left
  cases right
  cases trees
  rfl

/-- No two rows of a table share a primary key, and so no row repeats. -/
theorem toRelation_keyed {rows : Rows key} : rows.toRelation.Keyed key := by
  apply Relation.keyed_ofList.mpr
  rw [Relational.Keyed, List.map_map, List.Nodup, List.pairwise_map]
  refine Std.ExtTreeMap.distinct_keys_toList.imp_of_mem fun leftMember rightMember differ same ↦ ?_
  have leftKey := rows.keyed _ _ (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp leftMember)
  have rightKey := rows.keyed _ _ (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp rightMember)
  apply differ
  simp only [Function.comp] at same
  rw [← leftKey, ← rightKey, same]
  exact Std.ReflCmp.compare_self

/-- A table's relation repeats no row. -/
theorem toRelation_distinct {rows : Rows key} : rows.toRelation.Keyed id :=
  (Relation.keyed_iff_mem.mp toRelation_keyed).1

/-- `count` counts the rows of the relation. -/
theorem count_eq {rows : Rows key} : rows.count = rows.toRelation.count := by
  simp only [toRelation, Relation.count_ofList, List.length_map, Std.ExtTreeMap.length_toList]
  rfl

theorem mem_keysInAnyOrder {rows : Rows key} {primary : Key} :
    primary ∈ rows.keysInAnyOrder ↔ ∃ row ∈ rows, key row = primary := by
  rw [keysInAnyOrder, Std.ExtTreeMap.mem_keys, ← Std.ExtTreeMap.contains_iff_mem]
  exact contains_iff

theorem mem_keys [Ord Key] [TreeOrd.Agrees Key] {rows : Rows key} {primary : Key} :
    primary ∈ rows.keys ↔ ∃ row ∈ rows, key row = primary :=
  mem_keysInAnyOrder

/-- `keys` lists the primary keys in strictly ascending order. -/
theorem keys_ascending [Ord Key] [TreeOrd.Agrees Key] {rows : Rows key} :
    rows.keys.Pairwise fun left right ↦ compare left right = .lt :=
  Std.ExtTreeMap.ordered_keys.imp fun below ↦ by rwa [← TreeOrd.Agrees.cmp_eq]

/-- `maxKey?` is a primary key of a row, at least that of every row. -/
theorem maxKey?_eq_some [Ord Key] [TreeOrd.Agrees Key] {rows : Rows key} {primary : Key} :
    rows.maxKey? = some primary ↔
      (∃ row ∈ rows, key row = primary) ∧ ∀ row ∈ rows, (compare (key row) primary).isLE := by
  simp only [← TreeOrd.Agrees.cmp_eq]
  rw [maxKey?, Std.ExtTreeMap.maxKey?_eq_some_iff_mem_and_forall, ← Std.ExtTreeMap.contains_iff_mem]
  refine and_congr contains_iff ⟨fun above row member ↦ ?_, fun above other present ↦ ?_⟩
  · exact above (key row) (Std.ExtTreeMap.contains_iff_mem.mp (contains_iff.mpr ⟨row, member, rfl⟩))
  · obtain ⟨row, member, rfl⟩ := contains_iff.mp (Std.ExtTreeMap.contains_iff_mem.mpr present)
    exact above row member

theorem maxKey?_eq_none [Ord Key] [TreeOrd.Agrees Key] {rows : Rows key} :
    rows.maxKey? = none ↔ ∀ row, row ∉ rows := by
  rw [maxKey?, Std.ExtTreeMap.maxKey?_eq_none_iff]
  constructor
  · rintro empty row member
    have : rows.tree[key row]? = some row := member
    simp [empty] at this
  · intro absent
    apply Std.ExtTreeMap.ext_getElem?
    intro primary
    rw [Std.ExtTreeMap.getElem?_empty]
    cases found : rows.tree[primary]? with
    | none => rfl
    | some row => exact absurd (find?_eq_some.mp found).1 (absent row)

theorem mem_insertIfNew {rows : Rows key} {row other : Row} :
    other ∈ rows.insertIfNew row ↔ other ∈ rows ∨ (other = row ∧ rows.contains (key row) = false) := by
  unfold insertIfNew
  split
  · rename_i present
    simp [contains, present]
  · rename_i absent
    show (rows.tree.insert (key row) row)[key other]? = some other ↔ _
    rw [Std.ExtTreeMap.getElem?_insert]
    have absent : rows.contains (key row) = false := Bool.eq_false_iff.mpr absent
    split
    · rename_i same
      have same := Std.LawfulEqCmp.eq_of_compare same
      simp only [Option.some.injEq, absent, and_true]
      constructor
      · intro equal
        exact Or.inr equal.symm
      · rintro (member | equal)
        · exact absurd (contains_iff.mpr ⟨other, member, same.symm⟩) (by simp [absent])
        · exact equal.symm
    · rename_i differs
      constructor
      · exact Or.inl
      · rintro (member | ⟨rfl, _⟩)
        · exact member
        · exact absurd Std.ReflCmp.compare_self differs

theorem insert?_eq_none [DecidableEq Row] {rows : Rows key} {row : Row} :
    rows.insert? row = none ↔ ∃ other ∈ rows, key other = key row ∧ other ≠ row := by
  unfold insert?
  split
  · rename_i existing found
    obtain ⟨member, same⟩ := find?_eq_some.mp found
    split
    · rename_i equal
      simp only [reduceCtorEq, false_iff, not_exists, not_and, Decidable.not_not]
      intro other otherMember otherSame
      exact (key_injective otherMember member (otherSame.trans same.symm)).trans equal
    · rename_i differs
      simp only [true_iff]
      exact ⟨existing, member, same, differs⟩
  · rename_i absent
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro other member same
    have := find?_eq_some.mpr ⟨member, same⟩
    simp [absent] at this

theorem mem_insert? [DecidableEq Row] {rows next : Rows key} {row : Row}
    (inserted : rows.insert? row = some next) {other : Row} :
    other ∈ next ↔ other ∈ rows ∨ other = row := by
  unfold insert? at inserted
  split at inserted
  · rename_i existing found
    split at inserted
    · rename_i equal
      cases inserted
      subst equal
      constructor
      · exact Or.inl
      · rintro (member | rfl)
        · exact member
        · exact (find?_eq_some.mp found).1
    · cases inserted
  · rename_i absent
    cases inserted
    rw [mem_insertIfNew]
    have : rows.contains (key row) = false := by
      cases present : rows.contains (key row) with
      | false => rfl
      | true =>
        obtain ⟨existing, member, same⟩ := contains_iff.mp present
        have := find?_eq_some.mpr ⟨member, same⟩
        simp [absent] at this
    simp [this]

/-- What `insertAll?` refuses is a row of `added` whose primary key a different row has, of the
table or of `added`. -/
theorem insertAll?_eq_error [DecidableEq Row] :
    ∀ {rows : Rows key} {added : List Row} {row : Row}, rows.insertAll? added = .error row →
      row ∈ added ∧ ∃ other, (other ∈ rows ∨ other ∈ added) ∧ key other = key row ∧ other ≠ row
  | _, [], _, refused => by simp [insertAll?] at refused
  | rows, first :: rest, row, refused => by
    unfold insertAll? at refused
    split at refused
    · rename_i clash
      cases refused
      obtain ⟨other, member, same, differs⟩ := insert?_eq_none.mp clash
      exact ⟨List.mem_cons_self, other, Or.inl member, same, differs⟩
    · rename_i next inserted
      obtain ⟨later, other, member, same, differs⟩ := insertAll?_eq_error refused
      refine ⟨List.mem_cons_of_mem _ later, other, ?_, same, differs⟩
      rcases member with member | member
      · rcases (mem_insert? inserted).mp member with member | rfl
        · exact Or.inl member
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ member)

/-- What `insertAll?` accepts has exactly the rows of the table and of `added`. -/
theorem mem_insertAll? [DecidableEq Row] :
    ∀ {rows next : Rows key} {added : List Row}, rows.insertAll? added = .ok next →
      ∀ row, row ∈ next ↔ row ∈ rows ∨ row ∈ added
  | rows, next, [], accepted, row => by
    cases accepted
    simp
  | rows, next, first :: rest, accepted, row => by
    unfold insertAll? at accepted
    split at accepted
    · cases accepted
    · rename_i middle inserted
      rw [mem_insertAll? accepted, mem_insert? inserted, List.mem_cons]
      constructor
      · rintro ((member | rfl) | later)
        · exact Or.inl member
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr later)
      · rintro (member | rfl | later)
        · exact Or.inl (Or.inl member)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr later

/-- `insertAll?` succeeds where no two different rows, of the table or added, share a primary
key. -/
theorem insertAll?_ok [DecidableEq Row] :
    ∀ {rows : Rows key} {added : List Row},
      (∀ a b, (a ∈ rows ∨ a ∈ added) → (b ∈ rows ∨ b ∈ added) → key a = key b → a = b) →
      ∃ next, rows.insertAll? added = .ok next
  | rows, [], _ => ⟨rows, rfl⟩
  | rows, first :: rest, agree => by
    unfold insertAll?
    split
    · rename_i refused
      obtain ⟨other, member, same, differs⟩ := insert?_eq_none.mp refused
      exact absurd (agree other first (Or.inl member) (Or.inr List.mem_cons_self) same) differs
    · rename_i middle inserted
      refine insertAll?_ok fun a b inA inB same ↦ agree a b ?_ ?_ same
      · rcases inA with member | member
        · rcases (mem_insert? inserted).mp member with member | rfl
          · exact Or.inl member
          · exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ member)
      · rcases inB with member | member
        · rcases (mem_insert? inserted).mp member with member | rfl
          · exact Or.inl member
          · exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ member)

theorem find?_eq_none {rows : Rows key} {primary : Key} :
    rows.find? primary = none ↔ ∀ row ∈ rows, key row ≠ primary := by
  constructor
  · intro none row member same
    rw [find?_eq_some.mpr ⟨member, same⟩] at none
    cases none
  · intro absent
    cases found : rows.find? primary with
    | none => rfl
    | some row => exact absurd (find?_eq_some.mp found).2 (absent row (find?_eq_some.mp found).1)

/-- After `insertIfNew` of a row whose key the table lacks, the table's rows and the row. -/
theorem insertIfNew_of_fresh {rows : Rows key} {row : Row} (fresh : rows.contains (key row) = false)
    {other : Row} : other ∈ rows.insertIfNew row ↔ other ∈ rows ∨ other = row := by
  rw [mem_insertIfNew]
  simp [fresh]

/-- A row that `test` accepts, if any: one pass over the rows, in O(n) time for n rows.  Which one,
where several are, is not said.  For generic code over every table, which must name one row;
`first?` finds the first where the key's order means something. -/
def any? (rows : Rows key) (test : Row → Bool) : Option Row :=
  (rows.tree.toList.find? fun (_, row) ↦ test row).map Prod.snd

/-- What `any?` finds is a row that `test` accepts. -/
theorem any?_eq_some {rows : Rows key} {test : Row → Bool} {row : Row}
    (found : rows.any? test = some row) : row ∈ rows ∧ test row = true := by
  obtain ⟨⟨primary, other⟩, first, same⟩ := Option.map_eq_some_iff.mp found
  simp only at same
  subst same
  have member := List.mem_of_find?_eq_some first
  have accepted := List.find?_some first
  rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at member
  have keyed := rows.keyed primary other member
  subst keyed
  exact ⟨member, accepted⟩

theorem any?_eq_none {rows : Rows key} {test : Row → Bool} :
    rows.any? test = none ↔ ∀ row ∈ rows, test row = false := by
  simp only [any?, Option.map_eq_none_iff, List.find?_eq_none, Prod.forall,
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, Bool.not_eq_true]
  constructor
  · intro holds row member
    exact holds (key row) row member
  · intro holds primary row found
    have same := rows.keyed primary row found
    subst same
    exact holds row found

/-- The first row, in the order of the primary keys, that `test` accepts (`any?`, for a key whose
order means something). -/
def first? [Ord Key] [TreeOrd.Agrees Key] (rows : Rows key) (test : Row → Bool) : Option Row :=
  rows.any? test

/-- What `first?` finds is a row that `test` accepts. -/
theorem first?_eq_some [Ord Key] [TreeOrd.Agrees Key] {rows : Rows key} {test : Row → Bool}
    {row : Row}
    (found : rows.first? test = some row) : row ∈ rows ∧ test row = true :=
  any?_eq_some found

theorem first?_eq_none [Ord Key] [TreeOrd.Agrees Key] {rows : Rows key} {test : Row → Bool} :
    rows.first? test = none ↔ ∀ row ∈ rows, test row = false :=
  any?_eq_none

/-- Every row of `previous` is a row of `next`. -/
@[expose] def Included (previous next : Rows key) : Prop := ∀ row ∈ previous, row ∈ next

/-- `Included`, by looking up every row of `previous` in `next`. -/
private def includedRows [DecidableEq Row] (previous next : Rows key) : Bool :=
  previous.tree.toList.all fun (primary, row) ↦ next.tree[primary]? == some row

private theorem includedRows_iff [DecidableEq Row] {previous next : Rows key} :
    includedRows previous next = true ↔ Included previous next := by
  simp only [includedRows, List.all_eq_true, beq_iff_eq, Prod.forall,
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
  constructor
  · intro holds row member
    exact holds (key row) row member
  · intro included primary row found
    have same := previous.keyed primary row found
    subst same
    exact included row found

/-- `Included`, decided at once when both are the same object in memory, as tables that a
transition left alone are, and otherwise by looking up every row of `previous` in `next`. -/
def included [DecidableEq Row] (previous next : Rows key) : Bool :=
  withPtrEq previous next (fun _ ↦ includedRows previous next) fun same ↦
    same ▸ includedRows_iff.mpr fun _ member ↦ member

theorem included_iff [DecidableEq Row] {previous next : Rows key} :
    included previous next = true ↔ Included previous next :=
  includedRows_iff

instance [DecidableEq Row] (previous next : Rows key) : Decidable (Included previous next) :=
  decidable_of_iff _ included_iff

theorem included_insert? [DecidableEq Row] {rows next : Rows key} {row : Row}
    (inserted : rows.insert? row = some next) : Included rows next :=
  fun _ member ↦ (mem_insert? inserted).mpr (Or.inl member)

end Rows

namespace Rows

variable {Row First Rest : Type} [TreeOrd First] [TreeOrd Rest] {key : Row → First × Rest}

/-- The first entry of `tree`, in the order of its keys, whose key is at or above `bound`. -/
private theorem getEntryGE?_eq_find? {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (tree : Std.ExtTreeMap α β cmp) (bound : α) :
    tree.getEntryGE? bound = tree.toList.find? fun entry ↦ (cmp entry.1 bound).isGE := by
  rcases tree with ⟨⟨tree⟩⟩
  induction tree using Quotient.inductionOn with
  | h tree =>
    letI : Ord α := ⟨cmp⟩
    haveI : Std.TransOrd α := inferInstanceAs (Std.TransCmp cmp)
    change Std.DTreeMap.Internal.Impl.Const.getEntryGE? bound tree.inner =
      (Std.DTreeMap.Internal.Impl.Const.toList tree.inner).find? _
    rw [Std.DTreeMap.Internal.Impl.Const.getEntryGE?_eq_map,
      Std.DTreeMap.Internal.Impl.getEntryGE?_eq_find? tree.wf.ordered,
      Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map, List.find?_map]
    rfl

/-- The first entry of `tree`, in the order of its keys, whose key is above `bound`. -/
private theorem getEntryGT?_eq_find? {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (tree : Std.ExtTreeMap α β cmp) (bound : α) :
    tree.getEntryGT? bound = tree.toList.find? fun entry ↦ cmp entry.1 bound == .gt := by
  rcases tree with ⟨⟨tree⟩⟩
  induction tree using Quotient.inductionOn with
  | h tree =>
    letI : Ord α := ⟨cmp⟩
    haveI : Std.TransOrd α := inferInstanceAs (Std.TransCmp cmp)
    change Std.DTreeMap.Internal.Impl.Const.getEntryGT? bound tree.inner =
      (Std.DTreeMap.Internal.Impl.Const.toList tree.inner).find? _
    rw [Std.DTreeMap.Internal.Impl.Const.getEntryGT?_eq_map,
      Std.DTreeMap.Internal.Impl.getEntryGT?_eq_find? tree.wf.ordered,
      Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map, List.find?_map]
    congr 2
    funext entry
    show (cmp entry.1 bound).isGT = (cmp entry.1 bound == .gt)
    cases cmp entry.1 bound <;> rfl

/-- The last entry of `tree`, in the order of its keys, whose key is below `bound`: the first of the
entries in reverse order. -/
private theorem getEntryLT?_eq_find? {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (tree : Std.ExtTreeMap α β cmp) (bound : α) :
    tree.getEntryLT? bound = tree.toList.reverse.find? fun entry ↦ cmp entry.1 bound == .lt := by
  rcases tree with ⟨⟨tree⟩⟩
  induction tree using Quotient.inductionOn with
  | h tree =>
    letI : Ord α := ⟨cmp⟩
    haveI : Std.TransOrd α := inferInstanceAs (Std.TransCmp cmp)
    change Std.DTreeMap.Internal.Impl.Const.getEntryLT? bound tree.inner =
      (Std.DTreeMap.Internal.Impl.Const.toList tree.inner).reverse.find? _
    rw [Std.DTreeMap.Internal.Impl.Const.getEntryLT?_eq_map,
      Std.DTreeMap.Internal.Impl.getEntryLT?_eq_findRev? tree.wf.ordered, List.findRev?_eq_find?_reverse,
      Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map, ← List.map_reverse, List.find?_map]
    congr 2
    funext entry
    show (cmp entry.1 bound).isLT = (cmp entry.1 bound == .lt)
    cases cmp entry.1 bound <;> rfl

/-- The rows of the entry given and of those after it in the order of the keys, as long as their keys
begin with `first`: the forward half of `underInAnyOrder`'s walk, which steps from an entry to the
next one above it, at most `fuel` times (`underInAnyOrder` gives it the number of rows, which never
runs out). -/
private def walk (rows : Rows key) (first : First) :
    Option ((First × Rest) × Row) → Nat → Array Row → Array Row
  | some (primary, row), fuel + 1, found =>
    if TreeOrd.cmp primary.1 first == .eq then walk rows first (rows.tree.getEntryGT? primary) fuel (found.push row)
    else found
  | _, _, found => found

/-- The rows of the entry given and of those before it, in the order of the keys, as long as their
keys begin with `first`, before `found`: the backward half of `underInAnyOrder`'s walk, which steps
from an entry to the next one below it, at most `fuel` times. -/
private def walkBack (rows : Rows key) (first : First) :
    Option ((First × Rest) × Row) → Nat → List Row → List Row
  | some (primary, row), fuel + 1, found =>
    if TreeOrd.cmp primary.1 first == .eq then walkBack rows first (rows.tree.getEntryLT? primary) fuel (row :: found)
    else found
  | _, _, found => found

/-- The rows whose primary key begins with `first`, in an order that is not said: a search for a key
that begins with `first` (its rest any key's, the least's), then a step to the next key below and
above it for each row, in O((k + 1) log n) time for n rows of which k are listed.  For a key whose
rest has no order that means something (a record's), where what reads the rows needs none
(`Snapshot.citeAsInOrder`); `under` lists them in the order of the rest where it means something. -/
def underInAnyOrder (rows : Rows key) (first : First) : Array Row :=
  match rows.tree.minKey? with
  | none => #[]
  | some least =>
    (walkBack rows first (rows.tree.getEntryLT? (first, least.2)) rows.count []).toArray ++
      walk rows first (rows.tree.getEntryGE? (first, least.2)) rows.count #[]

/-- The rows whose primary key begins with `first`, in ascending order of the rest of the key: the
items of one record's list column, in position order, for a table keyed by record and position, by
the search of `underInAnyOrder`, whose order is the tree's; the key makes the order a strict one, so
there is no tie to refuse.  The order is that of the rest of the key, which must mean something: its
`Ord`, which the tree's order agrees with (`TreeOrd.Agrees`); the first part's order, a record's, is
a tree's only and is not read. -/
def under [Ord Rest] [TreeOrd.Agrees Rest] (rows : Rows key) (first : First) : Array Row :=
  rows.underInAnyOrder first

/-- The row of an entry, if its key begins with `first`. -/
private abbrev rowUnder (first : First) (entry : (First × Rest) × Row) : Option Row :=
  if TreeOrd.cmp entry.1.1 first == .eq then some entry.2 else none

/-- `walk` from the first entry of a stretch `entries` of the table's entries, every key of which
begins with `first` or something above it, lists the rows of the entries of the stretch whose keys
begin with `first`. -/
private theorem walk_eq (rows : Rows key) (first : First) :
    ∀ (entries before : List ((First × Rest) × Row)) (fuel : Nat) (found : Array Row),
      rows.tree.toList = before ++ entries → entries.length ≤ fuel →
      (∀ entry ∈ entries, TreeOrd.cmp entry.1.1 first ≠ .lt) →
      walk rows first entries.head? fuel found = found ++ (entries.filterMap (rowUnder first)).toArray
  | [], _, fuel, found, _, _, _ => by cases fuel <;> simp [walk]
  | (primary, row) :: rest, before, fuel + 1, found, split, short, above => by
    have ordered := Std.ExtTreeMap.ordered_keys_toList (t := rows.tree)
    rw [split, List.pairwise_append, List.pairwise_cons] at ordered
    by_cases begins : TreeOrd.cmp primary.1 first = .eq
    · have next : rows.tree.getEntryGT? primary = rest.head? := by
        rw [getEntryGT?_eq_find?, split, List.find?_append, List.find?_cons]
        have notBefore : before.find? (fun entry ↦ TreeOrd.cmp entry.1 primary == .gt) = none :=
          List.find?_eq_none.mpr fun entry member ↦ by
            simp [ordered.2.2 entry member (primary, row) (List.mem_cons_self ..)]
        cases rest with
        | nil => simp [notBefore, Std.ReflCmp.compare_self]
        | cons next later =>
          have above : TreeOrd.cmp next.1 primary = .gt :=
            Std.OrientedCmp.gt_of_lt (ordered.2.1.1 next (List.mem_cons_self ..))
          simp [notBefore, Std.ReflCmp.compare_self, above]
      simp only [List.head?_cons, walk, begins, beq_self_eq_true, ↓reduceIte, next]
      rw [walk_eq rows first rest (before ++ [(primary, row)]) fuel (found.push row) (by simp [split])
        (by simpa using short) fun entry member ↦ above entry (List.mem_cons_of_mem _ member)]
      simp [rowUnder, begins]
    · have beyond : TreeOrd.cmp primary.1 first = .gt := by
        cases order : TreeOrd.cmp primary.1 first
        · exact absurd order (above (primary, row) (List.mem_cons_self ..))
        · exact absurd order begins
        · rfl
      have none : rest.filterMap (rowUnder first) = [] := List.filterMap_eq_nil_iff.mpr fun entry member ↦ by
        have later : (TreeOrd.cmp primary.1 entry.1.1).then (TreeOrd.cmp primary.2 entry.1.2) = .lt :=
          ordered.2.1.1 entry member
        have notAbove : (TreeOrd.cmp primary.1 entry.1.1).isLE := by
          cases order : TreeOrd.cmp primary.1 entry.1.1 <;> simp_all [Ordering.then]
        have : TreeOrd.cmp entry.1.1 first = .gt :=
          Std.TransCmp.gt_of_isGE_of_gt (Std.OrientedCmp.isGE_of_isLE notAbove) beyond
        simp [rowUnder, this]
      simp [walk, begins, rowUnder, none]
  | _ :: _, _, 0, _, _, short, _ => by simp at short

/-- `walkBack` from the last entry of a stretch of the table's entries, `back` in reverse order, every
key of which begins with `first` or something below it, lists the rows of the entries of the stretch
whose keys begin with `first`, in the order of the keys, before `found`. -/
private theorem walkBack_eq (rows : Rows key) (first : First) :
    ∀ (back later : List ((First × Rest) × Row)) (fuel : Nat) (found : List Row),
      rows.tree.toList.reverse = later ++ back → back.length ≤ fuel →
      (∀ entry ∈ back, TreeOrd.cmp entry.1.1 first ≠ .gt) →
      walkBack rows first back.head? fuel found = back.reverse.filterMap (rowUnder first) ++ found
  | [], _, fuel, found, _, _, _ => by cases fuel <;> simp [walkBack]
  | (primary, row) :: rest, later, fuel + 1, found, split, short, below => by
    have ordered := List.pairwise_reverse.mpr (Std.ExtTreeMap.ordered_keys_toList (t := rows.tree))
    rw [split, List.pairwise_append, List.pairwise_cons] at ordered
    by_cases begins : TreeOrd.cmp primary.1 first = .eq
    · have next : rows.tree.getEntryLT? primary = rest.head? := by
        rw [getEntryLT?_eq_find?, split, List.find?_append, List.find?_cons]
        have notLater : later.find? (fun entry ↦ TreeOrd.cmp entry.1 primary == .lt) = none :=
          List.find?_eq_none.mpr fun entry member ↦ by
            simp [Std.OrientedCmp.gt_of_lt (ordered.2.2 entry member (primary, row) (List.mem_cons_self ..))]
        cases rest with
        | nil => simp [notLater, Std.ReflCmp.compare_self]
        | cons next earlier =>
          have below : TreeOrd.cmp next.1 primary = .lt := ordered.2.1.1 next (List.mem_cons_self ..)
          simp [notLater, Std.ReflCmp.compare_self, below]
      simp only [List.head?_cons, walkBack, begins, beq_self_eq_true, ↓reduceIte, next]
      rw [walkBack_eq rows first rest (later ++ [(primary, row)]) fuel (row :: found) (by simp [split])
        (by simpa using short) fun entry member ↦ below entry (List.mem_cons_of_mem _ member)]
      simp [rowUnder, begins]
    · have beneath : TreeOrd.cmp primary.1 first = .lt := by
        cases order : TreeOrd.cmp primary.1 first
        · rfl
        · exact absurd order begins
        · exact absurd order (below (primary, row) (List.mem_cons_self ..))
      have noneEarlier : rest.reverse.filterMap (rowUnder first) = [] :=
        List.filterMap_eq_nil_iff.mpr fun entry member ↦ by
          have earlier : (TreeOrd.cmp entry.1.1 primary.1).then (TreeOrd.cmp entry.1.2 primary.2) = .lt :=
            ordered.2.1.1 entry (List.mem_reverse.mp member)
          have notAbove : (TreeOrd.cmp entry.1.1 primary.1).isLE := by
            cases order : TreeOrd.cmp entry.1.1 primary.1 <;> simp_all [Ordering.then]
          have : TreeOrd.cmp entry.1.1 first = .lt := Std.TransCmp.lt_of_isLE_of_lt notAbove beneath
          simp [rowUnder, this]
      have notThis : rowUnder first (primary, row) = none := by simp [rowUnder, begins]
      simp only [List.head?_cons, walkBack, List.reverse_cons, List.filterMap_append, noneEarlier,
        notThis, List.filterMap_cons, List.filterMap_nil, List.nil_append]
      simp [beneath]
  | _ :: _, _, 0, _, _, short, _ => by simp at short

/-- `underInAnyOrder` lists the rows of the entries whose keys begin with `first`, in the order of the
keys. -/
private theorem underInAnyOrder_eq_filterMap (rows : Rows key) (first : First) :
    rows.underInAnyOrder first = (rows.tree.toList.filterMap fun (primary, row) ↦
      if TreeOrd.cmp primary.1 first == .eq then some row else none).toArray := by
  unfold underInAnyOrder
  cases found : rows.tree.minKey? with
  | none =>
    rw [Std.ExtTreeMap.minKey?_eq_none_iff] at found
    simp [found]
  | some least =>
  dsimp only
  let bound : First × Rest := (first, least.2)
  let below (entry : (First × Rest) × Row) : Bool := TreeOrd.cmp entry.1 bound == .lt
  have split := (List.takeWhile_append_dropWhile (p := below) (l := rows.tree.toList)).symm
  have ordered := Std.ExtTreeMap.ordered_keys_toList (t := rows.tree)
  have lowFirst : ∀ entry : (First × Rest) × Row, TreeOrd.cmp entry.1 bound = .lt →
      TreeOrd.cmp entry.1.1 first ≠ .gt := fun entry low above ↦ by
    change (TreeOrd.cmp entry.1.1 first).then _ = .lt at low
    simp [above, Ordering.then] at low
  -- the entries below the bound have keys that begin with `first` or something below it
  have early : ∀ entry ∈ rows.tree.toList.takeWhile below, TreeOrd.cmp entry.1 bound = .lt :=
    fun entry member ↦ by simpa [below] using List.all_eq_true.mp List.all_takeWhile entry member
  -- the rest are at or above the bound, so their keys begin with `first` or something above it
  have notBelow : ∀ entry ∈ rows.tree.toList.dropWhile below, TreeOrd.cmp entry.1 bound ≠ .lt := by
    have head := List.head?_dropWhile_not below rows.tree.toList
    have rest := ordered
    rw [split, List.pairwise_append] at rest
    intro entry member
    cases dropped : rows.tree.toList.dropWhile below with
    | nil => simp [dropped] at member
    | cons start later =>
      rw [dropped] at head member rest
      have startAbove : TreeOrd.cmp start.1 bound ≠ .lt := by simpa [below] using head
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ startAbove
      · intro low
        exact startAbove (Std.TransCmp.lt_trans ((List.pairwise_cons.mp rest.2.1).1 entry member) low)
  have late : ∀ entry ∈ rows.tree.toList.dropWhile below, TreeOrd.cmp entry.1.1 first ≠ .lt := by
    intro entry member low
    apply notBelow entry member
    change (TreeOrd.cmp entry.1.1 first).then _ = .lt
    simp [low, Ordering.then]
  have forward : rows.tree.getEntryGE? bound = (rows.tree.toList.dropWhile below).head? := by
    rw [getEntryGE?_eq_find?]
    conv => lhs; rw [split]
    rw [List.find?_append, List.find?_eq_none.mpr fun entry member ↦ by simp [early entry member]]
    cases dropped : rows.tree.toList.dropWhile below with
    | nil => rfl
    | cons start later =>
      have : (TreeOrd.cmp start.1 bound).isGE = true := by
        have := notBelow start (by simp [dropped])
        revert this
        cases TreeOrd.cmp start.1 bound <;> decide
      simp [this]
  have backward : rows.tree.getEntryLT? bound = (rows.tree.toList.takeWhile below).reverse.head? := by
    rw [getEntryLT?_eq_find?]
    conv => lhs; rw [split]
    rw [List.reverse_append, List.find?_append, List.find?_eq_none.mpr fun entry member ↦ by
      simp [notBelow entry (List.mem_reverse.mp member)]]
    cases taken : (rows.tree.toList.takeWhile below).reverse with
    | nil => rfl
    | cons last earlier =>
      have : TreeOrd.cmp last.1 bound = .lt := early last (List.mem_reverse.mp (by simp [taken]))
      simp [this]
  have count : rows.count = rows.tree.toList.length := (Std.ExtTreeMap.length_toList).symm
  rw [forward, backward, walk_eq rows first _ _ _ _ split
      (by rw [count]; exact (List.dropWhile_sublist below).length_le) late,
    walkBack_eq rows first _ (rows.tree.toList.dropWhile below).reverse _ _
      (by conv => lhs; rw [split]
          rw [List.reverse_append])
      (by rw [count, List.length_reverse]; exact (List.takeWhile_sublist below).length_le)
      (fun entry member ↦ lowFirst entry (early entry (List.mem_reverse.mp member)))]
  simp
  rw [← List.filterMap_append, ← split]

omit [TreeOrd Rest] in
/-- The entries whose keys begin with `first`, their rows: the rows that begin with it. -/
private theorem filterMap_entries (first : First) :
    ∀ (entries : List ((First × Rest) × Row)), (∀ entry ∈ entries, key entry.2 = entry.1) →
      entries.filterMap (fun (primary, row) ↦ if TreeOrd.cmp primary.1 first == .eq then some row else none) =
        (entries.map Prod.snd).filter fun row ↦ TreeOrd.cmp (key row).1 first == .eq
  | [], _ => rfl
  | (primary, row) :: rest, keyed => by
    have keyIs : key row = primary := keyed _ (List.mem_cons_self ..)
    have later := filterMap_entries first rest fun entry member ↦ keyed entry (List.mem_cons_of_mem _ member)
    by_cases begins : TreeOrd.cmp primary.1 first = .eq <;> simp [begins, later, keyIs]

/-- The rows `underInAnyOrder` lists, as a relation: the table's rows whose key begins with `first`,
as a selection over every row gives them. -/
theorem ofList_underInAnyOrder (rows : Rows key) (first : First) :
    Relation.ofList (rows.underInAnyOrder first).toList =
      rows.toRelation.select fun row ↦ TreeOrd.cmp (key row).1 first == .eq := by
  rw [underInAnyOrder_eq_filterMap, toRelation, Relation.select_ofList, List.toList_toArray,
    filterMap_entries first _ fun entry member ↦
      rows.keyed _ _ (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp member)]

theorem mem_underInAnyOrder {rows : Rows key} {first : First} {row : Row} :
    row ∈ rows.underInAnyOrder first ↔ row ∈ rows ∧ (key row).1 = first := by
  simp only [underInAnyOrder_eq_filterMap, List.mem_toArray, List.mem_filterMap]
  constructor
  · rintro ⟨⟨primary, other⟩, entry, found⟩
    simp only at found
    split at found
    · rename_i begins
      cases found
      have atKey := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp entry
      have keyIs := rows.keyed _ _ atKey
      subst keyIs
      exact ⟨atKey, Std.LawfulEqCmp.eq_of_compare (beq_iff_eq.mp begins)⟩
    · cases found
  · rintro ⟨member, rfl⟩
    refine ⟨(key row, row), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr member, ?_⟩
    simp [Std.ReflCmp.compare_self]

theorem mem_under [Ord Rest] [TreeOrd.Agrees Rest] {rows : Rows key} {first : First} {row : Row} :
    row ∈ rows.under first ↔ row ∈ rows ∧ (key row).1 = first :=
  mem_underInAnyOrder

/-- `under` lists the rows in strictly ascending order of the rest of the key. -/
theorem under_ascending [Ord Rest] [TreeOrd.Agrees Rest] {rows : Rows key} {first : First} :
    (rows.under first).toList.Pairwise fun left right ↦ compare (key left).2 (key right).2 = .lt := by
  simp only [under, underInAnyOrder_eq_filterMap, List.toList_toArray]
  apply (List.Pairwise.and_mem.mp (Std.ExtTreeMap.ordered_keys_toList (t := rows.tree))).filterMap
  rintro ⟨primary, row⟩ ⟨primary', row'⟩ ⟨entry, entry', below⟩ left found right found'
  simp only at found found'
  split at found <;> split at found' <;> try cases found <;> try cases found'
  rename_i begins begins'
  have keyIs := rows.keyed _ _ (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp entry)
  have keyIs' := rows.keyed _ _ (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp entry')
  rw [keyIs, keyIs']
  have same : primary.1 = primary'.1 :=
    (Std.LawfulEqCmp.eq_of_compare (beq_iff_eq.mp begins)).trans
      (Std.LawfulEqCmp.eq_of_compare (beq_iff_eq.mp begins')).symm
  have pair : (TreeOrd.cmp primary.1 primary'.1).then (TreeOrd.cmp primary.2 primary'.2) = .lt :=
    below
  rw [same, Std.ReflCmp.compare_self (cmp := (TreeOrd.cmp : First → First → Ordering))] at pair
  rw [← TreeOrd.Agrees.cmp_eq]
  exact pair

end Rows

/-- For the rows of a table with primary key `key`, the primary keys of the rows with each value
of `column`. -/
structure Index {Row Key Column : Type} [TreeOrd Key] [TreeOrd Column] (key : Row → Key)
    (column : Row → Column) where
  private mk ::
  private tree : Std.ExtTreeMap Column (Std.ExtTreeSet Key TreeOrd.cmp) TreeOrd.cmp

namespace Index

variable {Row Key Column : Type} [TreeOrd Key] [TreeOrd Column]
  {key : Row → Key} {column : Row → Column}

/-- The index of a table without rows. -/
def empty : Index key column := ⟨∅⟩

instance : EmptyCollection (Index key column) := ⟨empty⟩

/-- The primary keys under `value`. -/
def keysAt (index : Index key column) (value : Column) : Std.ExtTreeSet Key TreeOrd.cmp :=
  index.tree[value]?.getD ∅

/-- The index with `row` added. -/
def add (index : Index key column) (row : Row) : Index key column :=
  ⟨index.tree.insert (column row) ((index.keysAt (column row)).insert (key row))⟩

/-- The index lists primary key `primary` under `value`. -/
@[expose] def Lists (index : Index key column) (value : Column) (primary : Key) : Prop :=
  primary ∈ index.keysAt value

/-- The index lists exactly the rows of `rows`, each under its value of `column`. -/
@[expose] def Agrees (index : Index key column) (rows : Rows key) : Prop :=
  ∀ value primary, index.Lists value primary ↔ ∃ row ∈ rows, key row = primary ∧ column row = value

/-- The rows of `rows` listed under `value`. -/
def lookup (index : Index key column) (rows : Rows key) (value : Column) : Relation Row :=
  Relation.ofList ((index.keysAt value).toList.filterMap rows.find?)

/-- Through an index that agrees with the table, `lookup` selects the rows with `value`. -/
theorem mem_lookup {index : Index key column} {rows : Rows key} (agrees : index.Agrees rows)
    {value : Column} {row : Row} :
    row ∈ index.lookup rows value ↔ row ∈ rows ∧ column row = value := by
  simp only [lookup, Relation.mem_ofList, List.mem_filterMap, Std.ExtTreeSet.mem_toList]
  constructor
  · rintro ⟨primary, listed, found⟩
    obtain ⟨member, rfl⟩ := Rows.find?_eq_some.mp found
    obtain ⟨other, otherMember, same, otherValue⟩ := (agrees value (key row)).mp listed
    exact ⟨member, Rows.key_injective otherMember member same ▸ otherValue⟩
  · rintro ⟨member, rfl⟩
    exact ⟨key row, (agrees (column row) (key row)).mpr ⟨row, member, rfl, rfl⟩,
      Rows.find?_eq_some.mpr ⟨member, rfl⟩⟩

/-- `Agrees`, by looking up every row's key in the index and every listed key in the table. -/
def agrees (index : Index key column) (rows : Rows key) : Bool :=
  (rows.tree.toList.all fun (primary, row) ↦ (index.keysAt (column row)).contains primary) &&
    index.tree.toList.all fun (value, keys) ↦ keys.toList.all fun primary ↦
      match rows.tree[primary]? with
      | some row => TreeOrd.cmp (column row) value == .eq
      | none => false

theorem agrees_iff {index : Index key column} {rows : Rows key} :
    index.agrees rows = true ↔ index.Agrees rows := by
  simp only [agrees, Bool.and_eq_true, List.all_eq_true, Prod.forall,
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, Std.ExtTreeSet.mem_toList]
  constructor
  · rintro ⟨rowsListed, keysFound⟩ value primary
    constructor
    · intro listed
      unfold Lists keysAt at listed
      cases present : index.tree[value]? with
      | none => simp [present] at listed
      | some keys =>
        simp only [present, Option.getD_some] at listed
        have := keysFound value keys present primary listed
        split at this
        · rename_i row found
          have same := Std.LawfulEqCmp.eq_of_compare (beq_iff_eq.mp this)
          exact ⟨row, (Rows.find?_eq_some.mp found).1, (Rows.find?_eq_some.mp found).2, same⟩
        · cases this
    · rintro ⟨row, member, rfl, rfl⟩
      exact Std.ExtTreeSet.mem_iff_contains.mpr (rowsListed (key row) row member)
  · intro agreeing
    constructor
    · intro primary row found
      obtain ⟨member, rfl⟩ := Rows.find?_eq_some.mp found
      exact Std.ExtTreeSet.mem_iff_contains.mp ((agreeing _ _).mpr ⟨row, member, rfl, rfl⟩)
    · intro value keys present primary listed
      have : index.Lists value primary := by
        unfold Lists keysAt
        simp only [present, Option.getD_some]
        exact listed
      obtain ⟨row, member, rfl, rfl⟩ := (agreeing value primary).mp this
      have found : rows.tree[key row]? = some row := member
      simp [found, Std.ReflCmp.compare_self]


/-- The keys under `value` after adding `row`: those before, and `row`'s key under its value. -/
theorem lists_add {index : Index key column} {row : Row} {value : Column} {primary : Key} :
    (index.add row).Lists value primary ↔
      index.Lists value primary ∨ (column row = value ∧ key row = primary) := by
  unfold Lists keysAt add
  rw [Std.ExtTreeMap.getElem?_insert]
  split
  · rename_i same
    have same := Std.LawfulEqCmp.eq_of_compare same
    subst same
    simp only [Option.getD_some, Std.ExtTreeSet.mem_insert, true_and]
    constructor
    · rintro (equal | member)
      · exact Or.inr (Std.LawfulEqCmp.eq_of_compare equal)
      · exact Or.inl member
    · rintro (member | rfl)
      · exact Or.inr member
      · exact Or.inl Std.ReflCmp.compare_self
  · rename_i differs
    constructor
    · exact Or.inl
    · rintro (member | ⟨rfl, _⟩)
      · exact member
      · exact absurd Std.ReflCmp.compare_self differs

/-- An index that agrees with a table agrees, with a row added, with the table with the row added,
for a row whose primary key the table lacks. -/
theorem agrees_add {index : Index key column} {rows : Rows key} {row : Row}
    (agrees : index.Agrees rows) (fresh : rows.contains (key row) = false) :
    (index.add row).Agrees (rows.insertIfNew row) := by
  intro value primary
  rw [lists_add, agrees value primary]
  constructor
  · rintro (⟨other, member, same, equal⟩ | ⟨equal, same⟩)
    · exact ⟨other, Rows.mem_insertIfNew.mpr (Or.inl member), same, equal⟩
    · exact ⟨row, Rows.mem_insertIfNew.mpr (Or.inr ⟨rfl, fresh⟩), same, equal⟩
  · rintro ⟨other, member, same, equal⟩
    rcases Rows.mem_insertIfNew.mp member with member | ⟨rfl, _⟩
    · exact Or.inl ⟨other, member, same, equal⟩
    · exact Or.inr ⟨equal, same⟩

/-- Whether the index lists no key under `value` but `primary`, in O(log n) time. -/
def onlyAt (index : Index key column) (value : Column) (primary : Key) : Bool :=
  ((index.keysAt value).erase primary).isEmpty

theorem onlyAt_iff {index : Index key column} {value : Column} {primary : Key} :
    index.onlyAt value primary = true ↔ ∀ other, index.Lists value other → other = primary := by
  simp only [onlyAt, Lists, Std.ExtTreeSet.isEmpty_iff, Std.ExtTreeSet.ext_mem_iff,
    Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.not_mem_empty, iff_false, not_and]
  constructor
  · intro none other member
    exact Classical.byContradiction fun differs ↦ none other (fun same ↦ differs
      (Std.LawfulEqCmp.eq_of_compare same).symm) member
  · intro only other differs member
    exact differs (by rw [only other member]; exact Std.ReflCmp.compare_self)

/-- Whether the index lists some key under `value`, in O(log n) time. -/
def anyAt (index : Index key column) (value : Column) : Bool :=
  !(index.keysAt value).isEmpty

theorem anyAt_iff {index : Index key column} {value : Column} :
    index.anyAt value = true ↔ ∃ primary, index.Lists value primary := by
  simp only [anyAt, Lists, Bool.not_eq_true', Std.ExtTreeSet.isEmpty_eq_false_iff,
    Std.ExtTreeSet.ext_mem_iff, Std.ExtTreeSet.not_mem_empty, iff_false, Classical.not_forall,
    Classical.not_not]


theorem not_lists_empty {value : Column} {primary : Key} : ¬ (∅ : Index key column).Lists value primary := by
  show primary ∉ ((∅ : Std.ExtTreeMap Column (Std.ExtTreeSet Key TreeOrd.cmp) TreeOrd.cmp)[value]?.getD ∅)
  simp

/-- The keys under `value` after adding the rows of a list in turn. -/
theorem lists_foldl_add :
    ∀ {rows : List Row} {index : Index key column} {value : Column} {primary : Key},
      (rows.foldl add index).Lists value primary ↔
        index.Lists value primary ∨ ∃ row ∈ rows, column row = value ∧ key row = primary
  | [], _, _, _ => by simp
  | first :: rest, index, value, primary => by
    rw [List.foldl_cons, lists_foldl_add, lists_add]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((listed | added) | later)
      · exact Or.inl listed
      · exact Or.inr (Or.inl added)
      · exact Or.inr (Or.inr later)
    · rintro (listed | added | later)
      · exact Or.inl (Or.inl listed)
      · exact Or.inl (Or.inr added)
      · exact Or.inr later

/-- The index of the rows of a table, built by adding each, in O(n log n) time for n rows. -/
def ofRows (rows : Rows key) : Index key column := rows.toListInAnyOrder.foldl add ∅

theorem agrees_ofRows {rows : Rows key} : (ofRows rows : Index key column).Agrees rows := by
  intro value primary
  rw [ofRows, lists_foldl_add]
  simp only [not_lists_empty, false_or, Rows.mem_toListInAnyOrder]
  constructor
  · rintro ⟨row, member, value, primary⟩
    exact ⟨row, member, primary, value⟩
  · rintro ⟨row, member, primary, value⟩
    exact ⟨row, member, value, primary⟩

instance (index : Index key column) (rows : Rows key) : Decidable (index.Agrees rows) :=
  decidable_of_iff _ agrees_iff

end Index

end Relational
