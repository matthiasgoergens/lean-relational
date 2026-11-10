#!/usr/bin/env bash
# Generates S$n.lean (a schema of n plain root tables, id : Nat and x : Fin (i+1)) and T$n.lean (an
# executable that appends `count` one-row deltas to the last table) for n in 2 60 300.
cd "$(dirname "$0")" || exit 1
for n in 2 60 300; do
  {
    echo 'module'
    echo 'public import Relational.TableCommand'
    echo 'public import Relational.SchemaAudit'
    echo 'open Relational'
    echo '@[expose] public section'
    for i in $(seq 0 $((n-1))); do
      printf 'table%% t%d : R%d (id) in Snap\n  root%%\nwhere\n  id : Nat\n  x : Fin %d\n' $i $i $((i+1))
    done
    echo 'table_rows% Snap'
    echo 'table_defs% Snap'
    echo 'def schema : Schema Snap where'
    echo '  tables := declared_tables% Snap'
    echo '#audit_schema Snap schema'
  } > S$n.lean
  last=$((n-1))
  cat > T$n.lean <<EOT
import S$n
import Relational.SchemaLaws
import Relational.Db
open Relational

schema_laws% Snap schema
schema_coherence% schema

def step (db : Db schema) (i : Nat) : Except Refusal (Db schema) := do
  let grown ← db.append [t$last.insert ⟨i, 0⟩]
  return grown.next

def main (args : List String) : IO UInt32 := do
  let some count := args.head? >>= String.toNat? | IO.eprintln "usage: T$n count"; return 2
  let empty ← match Db.load schema {} with
    | .ok db => pure db
    | .error _ => IO.eprintln "empty refused"; return 1
  match (List.range count).foldlM step empty with
  | .ok db => IO.println s!"{count} {(t$last.rows db.rows).count}"; return 0
  | .error _ => IO.eprintln "refused"; return 1
EOT
done
