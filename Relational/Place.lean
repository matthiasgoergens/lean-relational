module

public section

namespace Relational

/-! A place: a position in an append-only log, which orders what the log holds.  `Place` holds the
position from 0, the number of entries written before it, and has no arithmetic: a place is compared
with another, found in the log, or written out, never added to or subtracted from, so the place
before another is asked for by name (`prev?`), and a place cannot be confused with a count or an
index of something else.  It is written as its number from 1 (`number`), where it leaves the
program (a file, a message). -/

/-- A place in a log: the position `idx` from 0, the number of entries before it. -/
@[ext] structure Place where
  idx : Nat
  deriving DecidableEq, Hashable, Repr, Inhabited

namespace Place

/-- The place as text outside the program writes it: its number, from 1. -/
@[expose] def number (p : Place) : Nat := p.idx + 1

/-- The place numbered `n`, from 1, as text outside the program writes it; none for 0,
which numbers no place. -/
@[noinline] def ofNumber? : Nat → Option Place
  | 0 => none
  | n + 1 => some ⟨n⟩

/-- The place of the entry written after `count` entries. -/
@[expose] def after (count : Nat) : Place := ⟨count⟩

/-- The place right before `p`, if `p` is not the first. -/
@[expose] def prev? (p : Place) : Option Place :=
  match p.idx with
  | 0 => none
  | i + 1 => some ⟨i⟩

/-- The place right after `p`. -/
@[expose] def next (p : Place) : Place := ⟨p.idx + 1⟩

@[simp] theorem number_ofNumber? {n : Nat} {p : Place} (h : ofNumber? n = some p) : p.number = n := by
  cases n <;> simp_all [ofNumber?, number]
  cases h; rfl

@[simp] theorem ofNumber?_number (p : Place) : ofNumber? p.number = some p := by
  simp [ofNumber?, number]

@[simp] theorem after_idx (p : Place) : after p.idx = p := by simp [after]

@[simp] theorem idx_after (count : Nat) : (after count).idx = count := by simp [after]

theorem prev?_next (p : Place) : p.next.prev? = some p := by
  simp [next, prev?]

instance : LT Place := ⟨fun a b ↦ a.idx < b.idx⟩
instance : LE Place := ⟨fun a b ↦ a.idx ≤ b.idx⟩
instance (a b : Place) : Decidable (a < b) := inferInstanceAs (Decidable (a.idx < b.idx))
instance (a b : Place) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.idx ≤ b.idx))
instance : Ord Place := ⟨fun a b ↦ compare a.idx b.idx⟩

theorem lt_def {a b : Place} : a < b ↔ a.idx < b.idx := Iff.rfl
theorem le_def {a b : Place} : a ≤ b ↔ a.idx ≤ b.idx := Iff.rfl
theorem lt_irrefl (p : Place) : ¬p < p := Nat.lt_irrefl p.idx
theorem compare_eq_lt {a b : Place} : compare a b = .lt ↔ a < b := Nat.compare_eq_lt
instance : Max Place := ⟨fun a b ↦ if a ≤ b then b else a⟩
instance : Min Place := ⟨fun a b ↦ if a ≤ b then a else b⟩

/-- A place as fault texts write it: its number. -/
instance : ToString Place := ⟨fun p ↦ toString p.number⟩

instance : Std.TransOrd Place where
  eq_swap {a b} := Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering)) (a := a.idx) (b := b.idx)
  isLE_trans {a b c} h₁ h₂ :=
    Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering)) (a := a.idx) (b := b.idx) (c := c.idx) h₁ h₂

instance : Std.LawfulEqOrd Place where
  eq_of_compare {a b} h := by
    cases a; cases b
    have := Std.LawfulEqCmp.eq_of_compare (cmp := (compare : Nat → Nat → Ordering)) h
    simp_all

namespace Literals

/-- Place literals for tests and `#guard`s, opened with `open scoped Place.Literals`: a numeral is the
place's number, from 1, so `(1 : Place)` is the first place; 0 numbers no place and has no literal. -/
scoped instance instOfNat (n : Nat) : OfNat Place (n + 1) := ⟨⟨n⟩⟩

end Literals

end Place

end Relational
