module

public import Std.Data.ExtTreeMap

public section

namespace Relational

/-- The order a balanced tree keeps its keys in (`Rows`, `Relation`'s joins, `Index`): a total
order whose equal keys are equal, which is all a tree needs, and which need mean nothing.  A type
with a lawful `Ord` keeps its keys in that order (`TreeOrd.ofOrd`), and its `Ord` is the order that
means something, which only it can order a walk by: `Relation.sortedBy?`, `minBy` and `maxBy`
take an `Ord`, and `Rows.keys` and the other ordered walks of a table an `Ord` that the tree's order
agrees with (`TreeOrd.Agrees`).  An identity, a record's or a relation's key, has a `TreeOrd` of
its own and no `Ord`, so no sort, `compare` or ordered walk takes it: a walk reads an order column
instead (`RecordRows.recordsInOrder`, `placeOf?`), and code that needs no order says so
(`Rows.any?`, `keysInAnyOrder`).  `TreeOrd.cmp` is for the generic tables alone. -/
class TreeOrd (α : Type) where
  /-- The order. -/
  cmp : α → α → Ordering
  /-- It is a total order. -/
  trans : Std.TransCmp cmp
  /-- Keys it finds equal are equal. -/
  lawfulEq : Std.LawfulEqCmp cmp

instance {α : Type} [TreeOrd α] : Std.TransCmp (TreeOrd.cmp (α := α)) := TreeOrd.trans
instance {α : Type} [TreeOrd α] : Std.LawfulEqCmp (TreeOrd.cmp (α := α)) := TreeOrd.lawfulEq

/-- A lawful `Ord`'s order, for a type whose order means something. -/
instance (priority := low) TreeOrd.ofOrd {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] :
    TreeOrd α :=
  ⟨compare, inferInstance, inferInstance⟩

/-- Pairs in the lexicographic order of their components' tree orders, for composite keys.  It is
the instance for every pair, whether or not its components have an `Ord`, so that every tree over
pairs of one type is kept in one order. -/
instance (priority := high) TreeOrd.prod {α β : Type} [TreeOrd α] [TreeOrd β] : TreeOrd (α × β) :=
  letI : Ord α := ⟨TreeOrd.cmp⟩
  letI : Ord β := ⟨TreeOrd.cmp⟩
  haveI : Std.TransOrd α := inferInstanceAs (Std.TransCmp (TreeOrd.cmp (α := α)))
  haveI : Std.TransOrd β := inferInstanceAs (Std.TransCmp (TreeOrd.cmp (α := β)))
  haveI : Std.LawfulEqOrd α := inferInstanceAs (Std.LawfulEqCmp (TreeOrd.cmp (α := α)))
  haveI : Std.LawfulEqOrd β := inferInstanceAs (Std.LawfulEqCmp (TreeOrd.cmp (α := β)))
  letI : Ord (α × β) := lexOrd
  ⟨compare, inferInstance, inferInstance⟩

/-- A type whose tree order is its `Ord`'s, so that a walk of a tree in its order ascends by
`compare`: what the ordered walks of a table need (`Rows.keys`, `toList`, `maxKey?`, `above`,
`first?`).  A tree order taken from the `Ord` agrees by definition, and pairs of agreeing
components agree under the lexicographic `Ord` (`open scoped Relational.CompositeKeys`). -/
class TreeOrd.Agrees (α : Type) [Ord α] [TreeOrd α] : Prop where
  /-- The tree's order is `compare`. -/
  cmp_eq : ∀ a b : α, TreeOrd.cmp a b = compare a b

instance TreeOrd.Agrees.ofOrd {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] :
    @TreeOrd.Agrees α _ TreeOrd.ofOrd :=
  ⟨fun _ _ ↦ rfl⟩

instance TreeOrd.Agrees.prod {α β : Type} [Ord α] [Ord β] [TreeOrd α] [TreeOrd β]
    [TreeOrd.Agrees α] [TreeOrd.Agrees β] : @TreeOrd.Agrees (α × β) lexOrd TreeOrd.prod :=
  @TreeOrd.Agrees.mk (α × β) lexOrd TreeOrd.prod fun a b ↦ by
    show (TreeOrd.cmp a.1 b.1).then (TreeOrd.cmp a.2 b.2) = (compare a.1 b.1).then (compare a.2 b.2)
    rw [TreeOrd.Agrees.cmp_eq a.1 b.1, TreeOrd.Agrees.cmp_eq a.2 b.2]

-- Checks: a type with a lawful `Ord` is kept in its `compare` order, and pairs lexicographically.
example : (TreeOrd.cmp : Nat → Nat → Ordering) = compare := rfl
example : TreeOrd.cmp ((1, 5) : Nat × Nat) (2, 0) = .lt := rfl
example : TreeOrd.cmp ((1, 5) : Nat × Nat) (1, 3) = .gt := rfl

end Relational
