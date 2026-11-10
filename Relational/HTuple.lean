module

public import Init

public section

namespace Relational

/-! A tuple with one component per element of a list, each of a type that depends on the element:
the indexes a database keeps, one per table and constraint, each of the types of its table's rows
and its constraint's column.  A nested product, so that it lives in `Type` whatever the universe
of the list's elements (a list of tables, each of which holds types). -/

/-- One value of type `f a` for each element `a` of the list. -/
@[expose] def HTuple {α : Type u} (f : α → Type) : List α → Type
  | [] => PUnit
  | a :: as => f a × HTuple f as

namespace HTuple

variable {α : Type u} {f : α → Type}

/-- The component at position `i`. -/
@[expose] def get : {l : List α} → HTuple f l → (i : Fin l.length) → f l[i]
  | _ :: _, tuple, ⟨0, _⟩ => (tuple : _ × _).1
  | _ :: _, tuple, ⟨i + 1, bound⟩ => get (tuple : _ × _).2 ⟨i, Nat.lt_of_succ_lt_succ bound⟩

/-- The tuple with the component at position `i` replaced by `change` of it. -/
@[expose] def modify : {l : List α} → HTuple f l → (i : Fin l.length) → (f l[i] → f l[i]) → HTuple f l
  | _ :: _, tuple, ⟨0, _⟩, change => ((change (tuple : _ × _).1), (tuple : _ × _).2)
  | _ :: _, tuple, ⟨i + 1, bound⟩, change =>
    ((tuple : _ × _).1, modify (tuple : _ × _).2 ⟨i, Nat.lt_of_succ_lt_succ bound⟩ change)

/-- The tuple with every component replaced by `change` of it. -/
@[expose] def map (change : (a : α) → f a → f a) : {l : List α} → HTuple f l → HTuple f l
  | [], tuple => tuple
  | a :: _, tuple => (change a (tuple : _ × _).1, map change (tuple : _ × _).2)

/-- The tuple of `make a` for each element `a`. -/
@[expose] def build (make : (a : α) → f a) : (l : List α) → HTuple f l
  | [] => PUnit.unit
  | a :: as => (make a, build make as)

/-- Whether `test` holds of every element and its component, in order. -/
@[expose] def all (test : (a : α) → f a → Bool) : {l : List α} → HTuple f l → Bool
  | [], _ => true
  | a :: _, tuple => test a (tuple : _ × _).1 && all test (tuple : _ × _).2

theorem get_modify_self : ∀ {l : List α} (tuple : HTuple f l) (i : Fin l.length) (change : f l[i] → f l[i]),
    (tuple.modify i change).get i = change (tuple.get i)
  | _ :: _, _, ⟨0, _⟩, _ => rfl
  | _ :: _, tuple, ⟨i + 1, bound⟩, change =>
    get_modify_self (l := _) (tuple : _ × _).2 ⟨i, Nat.lt_of_succ_lt_succ bound⟩ change

theorem get_modify_ne : ∀ {l : List α} (tuple : HTuple f l) (i j : Fin l.length) (change : f l[i] → f l[i]),
    i ≠ j → (tuple.modify i change).get j = tuple.get j
  | _ :: _, _, ⟨0, _⟩, ⟨0, _⟩, _, differs => absurd rfl differs
  | _ :: _, _, ⟨0, _⟩, ⟨_ + 1, _⟩, _, _ => rfl
  | _ :: _, _, ⟨_ + 1, _⟩, ⟨0, _⟩, _, _ => rfl
  | _ :: _, tuple, ⟨i + 1, bound⟩, ⟨j + 1, bound'⟩, change, differs =>
    get_modify_ne (l := _) (tuple : _ × _).2 ⟨i, Nat.lt_of_succ_lt_succ bound⟩
      ⟨j, Nat.lt_of_succ_lt_succ bound'⟩ change fun same ↦ differs (by cases same; rfl)

theorem get_map (change : (a : α) → f a → f a) :
    ∀ {l : List α} (tuple : HTuple f l) (i : Fin l.length),
      (tuple.map change).get i = change l[i] (tuple.get i)
  | _ :: _, _, ⟨0, _⟩ => rfl
  | _ :: _, tuple, ⟨i + 1, bound⟩ =>
    get_map change (l := _) (tuple : _ × _).2 ⟨i, Nat.lt_of_succ_lt_succ bound⟩

theorem get_build (make : (a : α) → f a) :
    ∀ (l : List α) (i : Fin l.length), (build make l).get i = make l[i]
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: rest, ⟨i + 1, bound⟩ => get_build make rest ⟨i, Nat.lt_of_succ_lt_succ bound⟩

theorem all_iff (test : (a : α) → f a → Bool) :
    ∀ {l : List α} (tuple : HTuple f l), tuple.all test = true ↔ ∀ i : Fin l.length, test l[i] (tuple.get i) = true
  | [], _ => ⟨fun _ i ↦ absurd i.isLt (Nat.not_lt_zero _), fun _ ↦ rfl⟩
  | a :: rest, tuple => by
    rw [all, Bool.and_eq_true, all_iff test (tuple : _ × _).2]
    constructor
    · rintro ⟨first, later⟩ ⟨i, bound⟩
      cases i with
      | zero => exact first
      | succ i => exact later ⟨i, Nat.lt_of_succ_lt_succ bound⟩
    · intro every
      exact ⟨every ⟨0, Nat.zero_lt_succ _⟩, fun ⟨i, bound⟩ ↦ every ⟨i + 1, Nat.succ_lt_succ bound⟩⟩

end HTuple

end Relational
