module

public import Std.Data.HashSet

public section

namespace Relational

@[expose] def Keyed (rows : List Row) (key : Row → Key) : Prop := (rows.map key).Nodup

@[expose] def References (children : List Child) (reference : Child → Key)
    (parents : List Parent) (key : Parent → Key) : Prop :=
  ∀ child ∈ children, ∃ parent ∈ parents, key parent = reference child

/-- One pass over `keys`, with the keys seen so far in a hash set. -/
@[specialize] def nodupFrom {Key : Type} [BEq Key] [Hashable Key] : List Key → Std.HashSet Key → Bool
  | [], _ => true
  | key :: rest, seen => !seen.contains key && nodupFrom rest (seen.insert key)

theorem nodupFrom_iff {Key : Type} [DecidableEq Key] [Hashable Key] (keys : List Key)
    (seen : Std.HashSet Key) :
    nodupFrom keys seen = true ↔ keys.Nodup ∧ ∀ key ∈ keys, seen.contains key = false := by
  induction keys generalizing seen with
  | nil => simp [nodupFrom]
  | cons key rest ih =>
    simp only [nodupFrom, Bool.and_eq_true, Bool.not_eq_true', ih, Std.HashSet.contains_insert,
      Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.nodup_cons, List.mem_cons,
      forall_eq_or_imp]
    constructor
    · rintro ⟨fresh, nodup, later⟩
      exact ⟨⟨fun mem ↦ (later key mem).1 rfl, nodup⟩, fresh, fun other mem ↦ (later other mem).2⟩
    · rintro ⟨⟨absent, nodup⟩, fresh, later⟩
      exact ⟨fresh, nodup, fun other mem ↦
        ⟨fun same ↦ absent (same ▸ mem), later other mem⟩⟩

/-- Up to this many rows, comparing pairs costs less than allocating a hash set. -/
def smallRelation : Nat := 32

/-- Whether `rows` has at most `bound` elements, without walking past `bound`. -/
def atMost {Row : Type} : Nat → List Row → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | bound + 1, _ :: rest => atMost bound rest

/-- Whether some row has key `wanted`. -/
@[specialize] def anyKey {Row Key : Type} [BEq Key] (key : Row → Key) (wanted : Key) :
    List Row → Bool
  | [] => false
  | row :: rest => key row == wanted || anyKey key wanted rest

theorem anyKey_iff {Row Key : Type} [DecidableEq Key] (key : Row → Key) (wanted : Key)
    (rows : List Row) : anyKey key wanted rows = true ↔ ∃ row ∈ rows, key row = wanted := by
  induction rows with
  | nil => simp [anyKey]
  | cons row rest ih => simp [anyKey, ih]

/-- Whether no two rows share a key, comparing each pair once. -/
@[specialize] def nodupRows {Row Key : Type} [BEq Key] (key : Row → Key) : List Row → Bool
  | [] => true
  | row :: rest => !anyKey key (key row) rest && nodupRows key rest

theorem nodupRows_iff {Row Key : Type} [DecidableEq Key] (key : Row → Key) (rows : List Row) :
    nodupRows key rows = true ↔ Keyed rows key := by
  induction rows with
  | nil => simp [nodupRows, Keyed]
  | cons row rest ih =>
    have any := anyKey_iff key (key row) rest
    simp only [Keyed] at ih ⊢
    cases found : anyKey key (key row) rest <;> simp_all [nodupRows, List.nodup_cons, List.mem_map]

/-- Whether every child's reference is some parent's key, scanning the parents. -/
@[specialize] def allReferenced {Child Parent Key : Type} [BEq Key] (reference : Child → Key)
    (parents : List Parent) (key : Parent → Key) : List Child → Bool
  | [] => true
  | child :: rest =>
    anyKey key (reference child) parents && allReferenced reference parents key rest

theorem allReferenced_iff {Child Parent Key : Type} [DecidableEq Key] (reference : Child → Key)
    (parents : List Parent) (key : Parent → Key) (children : List Child) :
    allReferenced reference parents key children = true ↔
      References children reference parents key := by
  induction children with
  | nil => simp [allReferenced, References]
  | cons child rest ih =>
    simp only [References] at ih ⊢
    simp [allReferenced, ih, anyKey_iff]

/-- `Keyed`, decided by comparing pairs for small relations and with a hash set in one pass
otherwise. -/
@[inline] def keyedFast {Row Key : Type} [DecidableEq Key] [Hashable Key] (rows : List Row)
    (key : Row → Key) : Bool :=
  if atMost smallRelation rows then nodupRows key rows
  else nodupFrom (rows.map key) ∅

theorem keyedFast_iff {Row Key : Type} [DecidableEq Key] [Hashable Key] (rows : List Row)
    (key : Row → Key) : keyedFast rows key = true ↔ Keyed rows key := by
  unfold keyedFast
  split
  · exact nodupRows_iff key rows
  · simp [Keyed, nodupFrom_iff]

/-- `References`, decided by scanning the parents for small relations and by collecting their
keys in a hash set otherwise.  No parent is examined when there are no children. -/
@[inline] def referencesFast {Child Parent Key : Type} [DecidableEq Key] [Hashable Key]
    (children : List Child) (reference : Child → Key) (parents : List Parent)
    (key : Parent → Key) : Bool :=
  match children with
  | [] => true
  | _ :: _ =>
    if atMost smallRelation parents then allReferenced reference parents key children
    else
      let known := Std.HashSet.ofList (parents.map key)
      children.all fun child ↦ known.contains (reference child)

theorem referencesFast_iff {Child Parent Key : Type} [DecidableEq Key] [Hashable Key]
    (children : List Child) (reference : Child → Key) (parents : List Parent)
    (key : Parent → Key) :
    referencesFast children reference parents key = true ↔
      References children reference parents key := by
  unfold referencesFast
  split
  · simp [References]
  · split
    · exact allReferenced_iff reference parents key _
    · simp [References, Std.HashSet.contains_ofList, List.mem_map]

instance {Row Key : Type} [DecidableEq Key] [Hashable Key] (rows : List Row) (key : Row → Key) :
    Decidable (Keyed rows key) :=
  decidable_of_iff _ (keyedFast_iff rows key)

instance {Child Parent Key : Type} [DecidableEq Key] [Hashable Key] (children : List Child)
    (reference : Child → Key) (parents : List Parent) (key : Parent → Key) :
    Decidable (References children reference parents key) :=
  decidable_of_iff _ (referencesFast_iff children reference parents key)

end Relational
