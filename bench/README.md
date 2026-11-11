# Append benchmark

Two small programs that time `Db.append`.  Both build against the library in the checkout above them (`path = ".."`), so they measure the code as it stands.

## Appending n deltas (`bench/`)

`Main.lean` declares two tables, authors (primary key `id`, a further unique key on `name`) and books (primary key `id`, a foreign key `author` to authors, and a mandatory participation: every author has a book).  `appendbench n` starts from the empty database and appends n deltas one at a time, delta i being author i and book i, then prints the row counts.

What is timed is the whole process: the user CPU time that `/usr/bin/time` reports for `appendbench n`, including start-up (about 0.02 s, measured at n = 0) and building the deltas, not only the appends.  So time divided by n is an upper bound on the cost of an append, not the cost itself.

```
cd bench
lake build
./run.sh OUTDIR 3
```

`run.sh` runs every size (1000, 4000, 16000, 256000 and 1024000; override with `SIZES="..."`) once per block, in a fresh random order for each block, and writes `OUTDIR/runs.tsv` (block, order, n, user and system seconds, peak memory, one-minute load average at the start of the run) and `OUTDIR/env.txt` (library commit, Lean version, binary checksum, machine).  Write OUTDIR outside the repository.  Timing needs a machine that is not otherwise busy: read the load column.

To time the code before this change, check out the base commit `43ecc75` in a second worktree, copy `bench/lakefile.toml`, `bench/lake-manifest.json`, `bench/lean-toolchain`, `bench/run.sh` and `bench/Main.lean` into its `bench/`, and delete the four lines of `Main.lean` that import `Relational.SchemaLaws` and `Relational.Db` and run `schema_laws%` and `schema_coherence%`: before, `append` needed neither.  Then build and run as above.  The old `append` takes about 135 s at n = 16000, so leave the larger sizes out.

## Appending to a schema of many tables (`bench/tables/`)

The cost of an append also depends on the number of tables T of the schema.  `gen.sh` writes a schema of T plain tables for T = 2, 60 and 300 (`S$T.lean`, each table with `id : Nat` and `x : Fin (i + 1)`) and an executable `T$T.lean` that appends COUNT one-row deltas to the last table.  The generated files are not kept in the repository.

```
cd bench/tables
./gen.sh
lake build
./run.sh OUTDIR 3 50000
```

`run.sh` times each executable at count 0 and at COUNT in randomised blocks, in the same way, so the difference of the two is the cost of COUNT appends.  Building `T300` also compiles the `Coherent` instance for 300 tables: `lake env lean T300.lean` takes the time of that and of the proofs, which grows faster than the number of tables.
