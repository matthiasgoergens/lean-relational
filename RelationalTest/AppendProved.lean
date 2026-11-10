module

public import RelationalTest.Schema
-- the `#guard`s below run code from these imports
meta import RelationalTest.Schema
meta import Relational.Db

open Relational

/-! `Db.appendProved`, `Db.decideAccepts` and the one-row lemmas, used from a module other than the
schema's, as a caller uses them.  This section is not exposed: only what the library and the
schema's module expose is visible here. -/

public section

namespace RelationsCheck.AppendProved

/-! ### Appending a row by a proof

An author: a table with a further unique key, no foreign keys, and no participation or subtyping
reading it.  The caller knows that the database has no author with the new one's identifier or
name; the rest is decided. -/

example (db : Db schema) (author : Author)
    (fresh : ∀ old ∈ authors.rows db.rows, old.id = author.id → old = author)
    (unique : ∀ other ∈ authors.rows db.rows, other.name = author.name → other = author) :
    db.GrownBy [authors.insert author] :=
  db.appendProved _ (Schema.accepts_insert fresh
    (fun key member other otherMember same ↦ by
      simp only [authors, Table.loaded, Table.unique, Table.make, List.nil_append, List.mem_singleton] at member
      subst member
      exact unique other otherMember same)
    (fun _ member ↦ absurd member List.not_mem_nil) (by decide) (by decide) (by decide))

/-- A book, whose foreign key finds its author: a caller proves that from the author being in the
database, by unfolding the foreign key that `references%` built. -/
example (db : Db schema) (book : Book) (author : Author)
    (fresh : ∀ old ∈ books.rows db.rows, old.id = book.id → old = book)
    (unique : ∀ other ∈ books.rows db.rows, (other.author, other.title) = (book.author, book.title) →
      other = book)
    (present : author ∈ authors.rows db.rows) (wrote : author.id = book.author) :
    db.GrownBy [books.insert book] :=
  db.appendProved _ (Schema.accepts_insert fresh
    (fun key member other otherMember same ↦ by
      simp only [books, Table.root, Table.index, Table.references, Table.unique, Table.make,
        List.nil_append, List.mem_singleton] at member
      subst member
      exact unique other otherMember same)
    (fun foreign member ↦ by
      simp only [books, Table.root, Table.index, Table.references, Table.unique, Table.make,
        List.nil_append, List.mem_singleton] at member
      subst member
      exact ⟨author, Rows.mem_toRelation.mpr present, rfl, wrote⟩)
    (by decide) (by decide) (by decide))

/-! ### The one-row lemmas, each on its own -/

example (db : Db schema) (author : Author)
    (fresh : ∀ old ∈ authors.rows db.rows, old.id = author.id → old = author) :
    schema.KeysAgree db.rows [(authors.insert author : Insert schema)] :=
  Schema.keysAgree_singleton (insert := authors.insert author) fresh

example (db : Db schema) (author : Author)
    (agree : schema.KeysAgree db.rows [(authors.insert author : Insert schema)])
    (unique : ∀ other ∈ authors.rows db.rows, other.name = author.name → other = author) :
    Schema.UniqueAccepted [(authors.insert author : Insert schema)] (schema.applied db.rows [authors.insert author]) :=
  -- the condition is stated through the schema's table at the insert's position, which is
  -- `authors` up to definitional unfolding
  Schema.uniqueAccepted_singleton agree (show ∀ key ∈ authors.uniqueKeys, ∀ other ∈ authors.rows db.rows,
      key.key other = key.key author → other = author from fun key member other otherMember same ↦ by
    simp only [authors, Table.loaded, Table.unique, Table.make, List.nil_append, List.mem_singleton] at member
    subst member
    exact unique other otherMember same)

example (db : Db schema) (author : Author)
    (agree : schema.KeysAgree db.rows [(authors.insert author : Insert schema)]) :
    Schema.ForeignAccepted [(authors.insert author : Insert schema)] (schema.applied db.rows [authors.insert author]) :=
  Schema.foreignAccepted_singleton agree fun _ member ↦ absurd member List.not_mem_nil

example (s : Library) (author : Author) :
    Schema.ParticipationAccepted [(authors.insert author : Insert schema)] s :=
  Schema.participationAccepted_of_unread (by rw [Table.insert_position]; decide)

example (s : Library) (author : Author) :
    Schema.MemberAccepted [(authors.insert author : Insert schema)] s :=
  Schema.memberAccepted_of_unread (by rw [Table.insert_position]; decide)

example (s : Library) (author : Author) :
    Schema.CoverAccepted [(authors.insert author : Insert schema)] s :=
  Schema.coverAccepted_of_unread (by rw [Table.insert_position]; decide)

/-- The side conditions are not vacuous: the records are read by a participation and a subtyping,
so `decide` refutes the conditions for a record. -/
example (record : Record) :
    ¬ ∀ k, (schema.coherence.supertype k).position ≠ (records.insert record : Insert schema).position := by
  rw [Table.insert_position]
  decide

example (record : Record) :
    ¬ ∀ p j, (schema.coherence.participation p j).position ≠ (records.insert record : Insert schema).position := by
  rw [Table.insert_position]
  decide

/-! ### Deciding, then appending by the proof -/

/-- The database with `delta` appended through `appendProved`, where `decideAccepts` decides that
the delta is accepted. -/
def appendDecided (db : Db schema) (delta : List (Insert schema)) : Option (Db schema) :=
  match db.decideAccepts delta with
  | isTrue accepts => some (db.appendProved delta accepts).next
  | isFalse _ => none

/-- How many authors and books a database has. -/
def counts (db : Db schema) : Nat × Nat := ((authors.rows db.rows).count, (books.rows db.rows).count)

-- a new author and a book of hers are accepted, and appended
#guard (library.toOption.bind fun db ↦ (appendDecided db
    [authors.insert ⟨4, "Frances"⟩, books.insert ⟨13, 4, "Fortran"⟩]).map counts) == some (4, 4)

-- an author with a name another author has is refused, as `append` refuses it
#guard (library.toOption.map fun db ↦ (appendDecided db [authors.insert ⟨4, "Ada"⟩]).isNone) == some true
#guard (library.toOption.map fun db ↦ (db.append [authors.insert ⟨4, "Ada"⟩]).isOk) == some false

-- a book of an author the database lacks is refused
#guard (library.toOption.map fun db ↦ (appendDecided db [books.insert ⟨13, 9, "Lost"⟩]).isNone) == some true

-- `decideAccepts` agrees with `append` on these deltas
#guard (library.toOption.map fun db ↦ [
    [authors.insert ⟨4, "Frances"⟩], [authors.insert ⟨1, "Ada"⟩], [authors.insert ⟨1, "Eve"⟩],
    [books.insert ⟨13, 2, "Sketch"⟩], [books.insert ⟨13, 2, "Notes"⟩],
    [records.insert ⟨5, .claim, "unsourced"⟩],
    [records.insert ⟨5, .claim, "sourced"⟩, claimSources.insert ⟨5, "here"⟩, notes.insert ⟨5, "n"⟩]
  ].all fun delta ↦ @decide (schema.Accepts db.rows delta) (db.decideAccepts delta) ==
    (db.append delta).isOk) == some true

end RelationsCheck.AppendProved
