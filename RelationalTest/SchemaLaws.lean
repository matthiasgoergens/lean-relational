module

public import RelationalTest.Schema
public import Relational.SchemaLaws

open Relational

public section

/-! The laws of the test schemas' readers and writers, proved by `schema_laws%` in a module of
their own. -/

namespace RelationsCheck

#print axioms schema.laws.wiring
#print axioms schema.coherence

-- The laws use the standard axioms only (through the instances the row types use).
#print axioms schema.laws.outer_lawful
#print axioms schema.laws.F_lawful
#print axioms schema.laws.wired

-- A caller reads a table past writes to others through the bridges and the family's laws.
example (s : Library) (r : Rows Author.id) : books.rows (authors.set s r) = books.rows s := by
  rw [authors.set_F, books.rows_F, schema.laws.F_lawful.get_set_ne _ _ _ _ (by intro h; cases h)]
  rfl

-- And through the laws over positions, for any two tables of the schema.
example (s : Library) (r : Rows Author.id) :
    edges.rows (authors.set s r) = edges.rows s :=
  Schema.Wiring.rows_set_ne (schema := schema) ⟨0, by decide⟩ ⟨12, by decide⟩ (by decide) s r

namespace Command

schema_laws% Building schema
schema_coherence% schema

#print axioms schema.laws.wiring
#print axioms schema.coherence

end Command

end RelationsCheck

-- The incremental append and its theorems use the standard axioms only.
#print axioms Schema.accepts_iff
#print axioms Schema.refusal?_eq_none
#print axioms Schema.refusal?_sound
#print axioms Db.append
#print axioms Db.append_refused
#print axioms Db.append_accepted
#print axioms Db.appendProved
