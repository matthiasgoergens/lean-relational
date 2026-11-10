import Relational.SchemaAudit
import Relational.TableCommand
import Relational.SchemaLaws
import Relational.Db
open Relational

/-! Appends `n` deltas, one at a time, each an author and a book, to a schema with a further unique
key (an author's name), a foreign key (a book's author) and a mandatory participation (every author
has a book).  Run as `appendbench n`; time it from outside (CPU time of the process). -/

structure Author where
  id : Nat
  name : String
  deriving DecidableEq, Repr

structure Book where
  id : Nat
  author : Nat
  title : String
  deriving DecidableEq, Repr

structure Shelf where
  authors : Rows Author.id := {}
  books : Rows Book.id := {}

def authors := table% Shelf.authors (id)
  unique% (name)
  root%

def books := table% Shelf.books (id)
  references% author → authors
  mandatory% author → authors
  owner% author → authors

def schema : Schema Shelf where
  tables := tables% [authors, books]

#audit_schema Shelf schema
schema_laws% Shelf schema
schema_coherence% schema

def step (db : Db schema) (i : Nat) : Except Refusal (Db schema) := do
  let grown ← db.append [authors.insert ⟨i, s!"author {i}"⟩, books.insert ⟨i, i, s!"book {i}"⟩]
  return grown.next

def main (args : List String) : IO UInt32 := do
  let some n := args.head? >>= String.toNat? | IO.eprintln "usage: appendbench n"; return 2
  let empty ← match Db.load schema {} with
    | .ok db => pure db
    | .error _ => IO.eprintln "empty refused"; return 1
  match (List.range n).foldlM step empty with
  | .ok db => IO.println s!"{n} {(authors.rows db.rows).count} {(books.rows db.rows).count}"; return 0
  | .error _ => IO.eprintln "refused"; return 1
