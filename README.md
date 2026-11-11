# Relational

Finite relations and typed databases for Lean 4, on Lean core and [DeriveMapM](https://github.com/matthiasgoergens/derive-mapm) alone (no Mathlib, no Batteries).

- **`Relation Row`** is a finite relation with bag semantics: a quotient of lists by permutation, so no function of a relation can observe the order of the rows behind it.  Repeated rows are kept, as in SQL without `DISTINCT`; that a relation has no repeats is a key like any other (`Keyed id`), which `distinct` establishes.  Order that matters is data, a column read by `minBy`, `maxBy`, `maxByGroup` and `sortedBy?`; there is no `toList`.  It has `select`, `project`, joins (on a key through balanced trees, or on any predicate), `union`, `count`, `reduce` over a commutative monoid, and laws for each, stated by membership or by how often a row occurs (`multiplicity`).  Two relations are equal exactly when every row occurs in them equally often (`Relation.eq_iff_multiplicity`).
- **`Rows`** holds one table: a persistent balanced tree from the primary key to the row, so the key is unique by construction and an insert copies one path and shares the rest.  The tree is extensional (`Std.ExtTreeMap`), so two tables with the same rows are equal whatever order they were inserted in.  Queries see a table as a `Relation`.
- **`Table`** and **`Schema`** state a schema's constraints in the manner of SQL `CREATE TABLE`: further unique keys, foreign keys (optionally restricted to some parent rows), mandatory participations, indexes, subtypings and ownership.  `table%` declares a table and its row structure together.
- **`Db`** is a snapshot that satisfies its schema.  `Db.load` checks a snapshot; `Db.append` adds a delta and returns the new database only if every constraint still holds, deciding it from the rows the delta adds and the database's indexes, and otherwise names the table and the constraint that failed; it needs the laws and coherence that `schema_laws%` and `schema_coherence%` generate for the schema.  `Db.Grown db` is a database grown from `db` by appends only, so a step typed `Db schema → Except Refusal db.Grown` can only add rows.
- **`#audit_schema`** fails the build unless a schema covers its snapshot structure field by field, and **`#describe_schema`** describes a schema as data (and `SchemaDescription.write` as JSON), checked against the definitions when the module compiles.
- **`Place`** is a position in an append-only log, with no arithmetic: compared, found or written out, never added to.

Nothing that runs in a program built on it is `partial`; one helper of the schema audit, which runs while the schema compiles, is.  `RelationalTest/Schema.lean` declares a small schema (keys, foreign keys, participations, subtypings, ownership) and checks it with `#guard`s when it compiles.

## Installing

In `lakefile.toml`:

```toml
[[require]]
name = "Relational"
git = "https://github.com/matthiasgoergens/lean-relational"
rev = "main"
```

## Building

`lake build` builds the library and `lake test` builds the checks.  The toolchain is in `lean-toolchain`.

## Licence

Apache 2.0, in `LICENSE`.
