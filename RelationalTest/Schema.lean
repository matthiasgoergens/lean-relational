module

public import Relational.SchemaDescribe
public import Relational.TableCommand
-- the `#guard`s and `#eval`s below run code from these imports
meta import Relational.SchemaDescribe
meta import Relational.TableCommand

open Relational

-- exposed, so that `schema_laws%` (RelationalTest/SchemaLaws.lean) unfolds the tables
@[expose] public section

/-! A small schema checked when the project builds: `table%`, `unique%`, `references%` without a
restriction on the parent rows and restricted by a list of kinds, by a constant relation of the
kinds allowed at each end of an edge with each fact, and by a predicate, `mandatory%`, `index%` and
`subtypes%`, covering, exhaustive or neither, with members for one value, several values or a
family of values, and `root%`, `owner%` and `loaded%` elaborate, the schema audit passes and
refuses what it should, a delta that satisfies the schema is appended, every kind of constraint and
every kind of refusal of an append refuses a delta or snapshot that breaks it and names the table
and constraint, and queries read the rows only through relations and columns; and a database grown
from another keeps the rows of every owner that the other has, or the diagnosis names the table;
and a schema declared with the table command passes the audit, and the command refuses what it
should, where the refusal is. -/

namespace RelationsCheck

open scoped Relational.CompositeKeys

structure Author where
  id : Nat
  name : String
  deriving @[expose] DecidableEq, Repr

structure Book where
  id : Nat
  author : Nat
  title : String
  deriving @[expose] DecidableEq, Repr

inductive Kind where
  | claim
  | premise
  | verdict
  /-- A record of a kind that has no table of its own yet, by the kind's name. -/
  | tagged (tag : String)
  deriving @[expose] DecidableEq, Hashable, Repr

/-- Whether the kind is `tagged`, whatever its name. -/
def Kind.isTagged : Kind → Bool
  | .tagged _ => true
  | _ => false

/-- A row of the supertype table, keyed by its sequence number. -/
structure Record where
  seq : Nat
  kind : Kind
  text : String
  deriving @[expose] DecidableEq, Repr

/-- A verdict from the judge: a subtype of a verdict record. -/
structure JudgeVerdict where
  record : Nat
  holds : Bool
  deriving @[expose] DecidableEq, Repr

/-- A verdict from the gate: another subtype of a verdict record. -/
structure GateVerdict where
  record : Nat
  passed : Bool
  deriving @[expose] DecidableEq, Repr

/-- Where a claim comes from: every claim record has one. -/
structure ClaimSource where
  record : Nat
  source : String
  deriving @[expose] DecidableEq, Repr

/-- A premise quoted from the question: one of the two attributes a premise has exactly one of. -/
structure PremiseQuote where
  record : Nat
  quote : String
  deriving @[expose] DecidableEq, Repr

/-- A premise that links to another claim: the other of the two. -/
structure PremiseLink where
  record : Nat
  claim : Nat
  deriving @[expose] DecidableEq, Repr

/-- A note on a claim or a premise: a subtype for two kinds.  Every claim and premise has one. -/
structure Note where
  record : Nat
  note : String
  deriving @[expose] DecidableEq, Repr

/-- The body of a record of a tagged kind: a subtype for a family of kinds. -/
structure TaggedBody where
  record : Nat
  body : String
  deriving @[expose] DecidableEq, Repr

/-- A review of a record by one reviewer: a row that belongs to the record, keyed with it. -/
structure Review where
  record : Nat
  reviewer : String
  approves : Bool
  deriving @[expose] DecidableEq, Repr

/-- The answer to a review that does not approve: a row that belongs to the review, keyed with it,
by a foreign key on both columns. -/
structure ReviewReply where
  record : Nat
  reviewer : String
  text : String
  deriving @[expose] DecidableEq, Repr

/-- What an edge says, which decides the kinds of record it may join. -/
inductive EdgeFact where
  | judgedBy
  | premiseOf
  deriving @[expose] DecidableEq, Hashable, Repr

/-- The two ends of an edge. -/
inductive End where
  | source
  | target
  deriving @[expose] DecidableEq, Repr

/-- The kinds of record at each end of an edge with each fact, as data: a claim or a premise is
judged by a verdict, and a premise is a premise of a claim. -/
def edgeEnds : Allowance EdgeFact End Kind where
  name := "edgeEnds"
  rows := [
    (.judgedBy, .source, .claim), (.judgedBy, .source, .premise), (.judgedBy, .target, .verdict),
    (.premiseOf, .source, .premise), (.premiseOf, .target, .claim)]

/-- An edge from a claim or premise to a verdict or a claim, in the order of `position`. -/
structure Edge where
  position : Nat
  source : Nat
  target : Nat
  fact : EdgeFact
  deriving @[expose] DecidableEq, Repr

structure Library where
  authors : Rows Author.id := {}
  books : Rows Book.id := {}
  booksByAuthor : Index Book.id Book.author := {}
  records : Rows Record.seq := {}
  judgeVerdicts : Rows JudgeVerdict.record := {}
  gateVerdicts : Rows GateVerdict.record := {}
  claimSources : Rows ClaimSource.record := {}
  premiseQuotes : Rows PremiseQuote.record := {}
  premiseLinks : Rows PremiseLink.record := {}
  notes : Rows Note.record := {}
  taggedBodies : Rows TaggedBody.record := {}
  reviews : Rows (fun (review : Review) ↦ (review.record, review.reviewer)) := {}
  reviewReplies : Rows (fun (reply : ReviewReply) ↦ (reply.record, reply.reviewer)) := {}
  edges : Rows Edge.position := {}
  edgesBySource : Index Edge.position Edge.source := {}

/-- The authors, a catalogue that only the loader writes. -/
def authors := table% Library.authors (id)
  unique% (name)
  loaded%

def books := table% Library.books (id)
  unique% (author, title)
  references% author → authors
  index% Library.booksByAuthor
  root%

def records := table% Library.records (seq)
  root%

def judgeVerdicts := table% Library.judgeVerdicts (record)
  owner% record → records

def gateVerdicts := table% Library.gateVerdicts (record)
  owner% record → records

def claimSources := table% Library.claimSources (record)
  references% record → records kinds% kind [Kind.claim]
  mandatory% record → records for% fun record ↦ record.kind == Kind.claim
  owner% record → records

def premiseQuotes := table% Library.premiseQuotes (record)
  owner% record → records

/-- A premise links to an earlier claim: a rule that compares a column of the child row with one
of the parent row, which no constant relation states. -/
def premiseLinks := table% Library.premiseLinks (record)
  references% claim → records where% fun link record ↦
    record.kind == Kind.claim && decide (record.seq < link.record)
  owner% record → records

def notes := table% Library.notes (record)
  owner% record → records

def taggedBodies := table% Library.taggedBodies (record)
  owner% record → records

/-- Reviews belong to the record they review, through a foreign key that is part of their key. -/
def reviews := table% Library.reviews (record, reviewer)
  references% record → records
  owner% record → records

/-- A review that does not approve has a reply, and only such a review has one: a foreign key and a
mandatory participation on the two columns of the review's key, restricted by the review's row. -/
def reviewReplies := table% Library.reviewReplies (record, reviewer)
  references% record → records
  references% (record, reviewer) → reviews where% fun _ review ↦ !review.approves
  mandatory% (record, reviewer) → reviews for% fun review ↦ !review.approves
  owner% record → records

def edges := table% Library.edges (position)
  references% source → records allowed% edgeEnds (fact, End.source, kind)
  references% target → records allowed% edgeEnds (fact, End.target, kind)
  index% Library.edgesBySource
  root%

def schema : Schema Library where
  tables := tables% [authors, books, records, judgeVerdicts, gateVerdicts, claimSources,
    premiseQuotes, premiseLinks, notes, taggedBodies, reviews, reviewReplies, edges]
  subtypings := [
    subtypes% records (kind) [judgeVerdicts ↦ Kind.verdict, gateVerdicts ↦ Kind.verdict] covering%,
    subtypes% records (kind) [premiseQuotes ↦ Kind.premise, premiseLinks ↦ Kind.premise] covering%,
    subtypes% records (kind) [notes ↦ values% [Kind.claim, Kind.premise],
      taggedBodies ↦ family% Kind.isTagged] covering%]

#audit_schema Library schema
#describe_schema Library schema

-- The schema's description, built from the schema when this module is built: the parts that
-- matter, held here so that a change in the description shows.
#guard schema.description.tables.map (·.name) == ["authors", "books", "records", "judgeVerdicts",
  "gateVerdicts", "claimSources", "premiseQuotes", "premiseLinks", "notes", "taggedBodies", "reviews",
  "reviewReplies", "edges"]
#guard schema.description.tables.map (·.owner) == [.loaded, .root, .root,
  .owned "record" "records", .owned "record" "records", .owned "record" "records",
  .owned "record" "records", .owned "record" "records", .owned "record" "records",
  .owned "record" "records", .owned "record" "records", .owned "record" "records", .root]
#guard schema.description.table? "edges" == some {
  name := "edges"
  columns := [⟨"position", "Nat"⟩, ⟨"source", "Nat"⟩, ⟨"target", "Nat"⟩,
    ⟨"fact", "RelationsCheck.EdgeFact"⟩]
  primaryKey := ["position"]
  foreignKeys := [
    { column := "source", parent := "records"
      restriction := .allowance "fact" "edgeEnds" "source" "kind" },
    { column := "target", parent := "records"
      restriction := .allowance "fact" "edgeEnds" "target" "kind" }]
  indexes := [⟨"edgesBySource", "source"⟩]
  owner := .root }
#guard schema.description.allowances == [{
  name := "edgeEnds", childType := "RelationsCheck.EdgeFact", endpointType := "RelationsCheck.End"
  parentType := "RelationsCheck.Kind"
  rows := [⟨"judgedBy", "source", "claim"⟩, ⟨"judgedBy", "source", "premise"⟩,
    ⟨"judgedBy", "target", "verdict"⟩, ⟨"premiseOf", "source", "premise"⟩,
    ⟨"premiseOf", "target", "claim"⟩] }]
#guard (schema.description.table? "authors").map (·.uniqueKeys) == some [["name"]]
#guard (schema.description.table? "books").map (fun table ↦ (table.uniqueKeys, table.foreignKeys)) ==
  some ([["author", "title"]], [{ column := "author", parent := "authors" }])
#guard (schema.description.table? "claimSources").map (fun table ↦
    (table.foreignKeys, table.mandatory)) == some (
  [{ column := "record", parent := "records", restriction := .facts "kind" ["claim"] }],
  [{ column := "record", parent := "records", scope := .predicate }])
#guard (schema.description.table? "premiseLinks").map (·.foreignKeys) ==
  some [{ column := "claim", parent := "records", restriction := .predicate }]
#guard (schema.description.table? "reviewReplies").map (fun table ↦ (table.foreignKeys, table.mandatory)) ==
  some ([{ column := "record", parent := "records" },
      { column := "record, reviewer", parent := "reviews", restriction := .predicate }],
    [{ column := "record, reviewer", parent := "reviews", scope := .predicate }])
#guard schema.description.subtypings == [
  { supertype := "records", discriminator := "kind", coverage := .covering
    members := [⟨"judgeVerdicts", .values ["verdict"]⟩, ⟨"gateVerdicts", .values ["verdict"]⟩] },
  { supertype := "records", discriminator := "kind", coverage := .covering
    members := [⟨"premiseQuotes", .values ["premise"]⟩, ⟨"premiseLinks", .values ["premise"]⟩] },
  { supertype := "records", discriminator := "kind", coverage := .covering
    members := [⟨"notes", .values ["claim", "premise"]⟩, ⟨"taggedBodies", .predicate⟩] }]

/-- A schema that lists a subtype twice, for two values, which the audit refuses: a member with
several values lists them in one list. -/
def memberTwice : Schema Library where
  tables := schema.tables
  subtypings := [subtypes% records (kind) [notes ↦ Kind.claim, notes ↦ Kind.premise]]

/-- error: the subtype notes is listed twice for records -/
#guard_msgs in
#audit_schema Library memberTwice

/-- A schema with a subtype for no value, which the audit refuses. -/
def memberForNothing : Schema Library where
  tables := schema.tables
  subtypings := [subtypes% records (kind) [notes ↦ values% []]]

/-- error: the subtype notes of records is for no value -/
#guard_msgs in
#audit_schema Library memberForNothing

/-- A schema with a subtype that lists a value twice, which the audit refuses. -/
def valueTwice : Schema Library where
  tables := schema.tables
  subtypings := [subtypes% records (kind) [notes ↦ values% [Kind.claim, Kind.premise, Kind.claim]]]

/-- error: the subtype notes of records lists the value Kind.claim twice -/
#guard_msgs in
#audit_schema Library valueTwice

/-- A schema with an exhaustive subtyping without members, which would refuse every record and
which the audit refuses. -/
def exhaustiveOfNothing : Schema Library where
  tables := schema.tables
  subtypings := [subtypes% records (kind) [] exhaustive%]

/-- error: an exhaustive subtyping of records has no member, so it refuses every row -/
#guard_msgs in
#audit_schema Library exhaustiveOfNothing

/-- A schema that has not passed the audit, which the description refuses. -/
def unaudited : Schema Library where
  tables := tables% [authors]

/-- error: RelationsCheck.unaudited has not passed #audit_schema -/
#guard_msgs in
#describe_schema Library unaudited

/-- What an append or a load refused, if anything. -/
def refusal {Error Result : Type} : Except Error Result → Option Error
  | .ok _ => none
  | .error error => some error

def base : List (Insert schema) := [
  authors.insert ⟨1, "Ada"⟩, authors.insert ⟨2, "Grace"⟩, authors.insert ⟨3, "Barbara"⟩,
  books.insert ⟨10, 1, "Notes"⟩, books.insert ⟨11, 2, "Compilers"⟩,
  books.insert ⟨12, 1, "Sketch"⟩,
  records.insert ⟨1, .claim, "a claim"⟩, records.insert ⟨2, .premise, "a premise"⟩,
  records.insert ⟨3, .verdict, "it holds"⟩, records.insert ⟨4, .verdict, "it passes"⟩,
  judgeVerdicts.insert ⟨3, true⟩, gateVerdicts.insert ⟨4, false⟩,
  claimSources.insert ⟨1, "the question"⟩, premiseQuotes.insert ⟨2, "as given"⟩,
  notes.insert ⟨1, "checked"⟩, notes.insert ⟨2, "quoted"⟩,
  edges.insert ⟨0, 1, 3, .judgedBy⟩, edges.insert ⟨1, 2, 4, .judgedBy⟩,
  edges.insert ⟨2, 1, 4, .judgedBy⟩]

/-- The database of `base`, appended to the empty one. -/
def library : Except Refusal (Db schema) := do
  let empty ← (Db.load schema {}).mapError .invalid
  return (← empty.append base).next

/-- `library` with `delta` appended. -/
def grown (delta : List (Insert schema)) : Except Refusal (Db schema) := do
  return (← (← library).append delta).next

/-- A snapshot whose index does not list its books. -/
def staleSnapshot : Option Library := do
  let authors ← (Rows.ofList? [⟨1, "Ada"⟩] : Except Author (Rows Author.id)).toOption
  let books ← (Rows.ofList? [⟨10, 1, "Notes"⟩] : Except Book (Rows Book.id)).toOption
  return { authors, books }

-- Accepted.
#guard refusal library == none
#guard refusal (grown [books.insert ⟨13, 3, "Later"⟩, authors.insert ⟨4, "Edsger"⟩]) == none
-- Appending a row the table already has changes nothing, also twice in one delta.
#guard (grown [books.insert ⟨10, 1, "Notes"⟩, books.insert ⟨13, 3, "Later"⟩,
    books.insert ⟨13, 3, "Later"⟩]).toOption.map (·.rows.books.count) == some 4
-- An edge's allowed targets depend on its own fact: a premise of a claim is accepted.
#guard refusal (grown [edges.insert ⟨3, 2, 1, .premiseOf⟩]) == none
-- A foreign key and a mandatory participation on two columns: a review that does not approve, with
-- its reply, is accepted; a reply to no review, a reply to a review that approves, and a review
-- that does not approve without a reply are refused, each naming both columns.
#guard refusal (grown [reviews.insert ⟨1, "Ada", false⟩, reviewReplies.insert ⟨1, "Ada", "why"⟩]) == none
#guard refusal (grown [reviews.insert ⟨1, "Ada", false⟩, reviewReplies.insert ⟨1, "Ada", "why"⟩,
    reviewReplies.insert ⟨1, "Grace", "why"⟩]) ==
  some (.invalid (.dangling "reviewReplies" "record, reviewer"))
#guard refusal (grown [reviews.insert ⟨1, "Ada", true⟩, reviewReplies.insert ⟨1, "Ada", "why"⟩]) ==
  some (.invalid (.wrongKind "reviewReplies" "record, reviewer"))
#guard refusal (grown [reviews.insert ⟨1, "Ada", false⟩]) ==
  some (.invalid (.missing "reviewReplies" "record, reviewer"))
-- Refused, one vector per kind of refusal and constraint.
#guard refusal (grown [books.insert ⟨10, 2, "Again"⟩]) == some (.conflict "books" "id")
#guard refusal (grown [books.insert ⟨13, 2, "One"⟩, books.insert ⟨13, 3, "Other"⟩]) ==
  some (.conflict "books" "id")
-- Conflicts in two tables: the first table in the schema's order is named.
#guard refusal (grown [books.insert ⟨10, 2, "Again"⟩, authors.insert ⟨1, "Augusta"⟩]) ==
  some (.conflict "authors" "id")
#guard refusal (grown [authors.insert ⟨5, "Ada"⟩]) == some (.invalid (.duplicate "authors" "name"))
#guard refusal (grown [books.insert ⟨13, 1, "Notes"⟩]) ==
  some (.invalid (.duplicate "books" "author, title"))
#guard refusal (grown [books.insert ⟨13, 9, "Ghost"⟩]) == some (.invalid (.dangling "books" "author"))
#guard refusal (grown [edges.insert ⟨3, 9, 4, .judgedBy⟩]) ==
  some (.invalid (.dangling "edges" "source"))
#guard refusal (grown [edges.insert ⟨3, 3, 4, .judgedBy⟩]) ==
  some (.invalid (.wrongKind "edges" "source"))
#guard refusal (grown [edges.insert ⟨3, 1, 2, .judgedBy⟩]) ==
  some (.invalid (.wrongKind "edges" "target"))
#guard refusal (grown [edges.insert ⟨3, 2, 4, .premiseOf⟩]) ==
  some (.invalid (.wrongKind "edges" "target"))
-- A claim may be the source of a `judgedBy` edge but not of a `premiseOf` edge.
#guard refusal (grown [edges.insert ⟨3, 1, 1, .premiseOf⟩]) ==
  some (.invalid (.wrongKind "edges" "source"))
-- A premise links to a claim recorded before it, by a predicate.
#guard refusal (grown [records.insert ⟨5, .premise, "later"⟩, records.insert ⟨6, .claim, "newer"⟩,
    claimSources.insert ⟨6, "the question"⟩, premiseLinks.insert ⟨5, 6⟩]) ==
  some (.invalid (.wrongKind "premiseLinks" "claim"))
-- A row that dangles and a row of the wrong kind in one column: the dangling one is reported.
#guard refusal (grown [edges.insert ⟨3, 3, 4, .judgedBy⟩, edges.insert ⟨4, 9, 4, .judgedBy⟩]) ==
  some (.invalid (.dangling "edges" "source"))
-- A subtype row hangs off a supertype row of its subtyping's fact, without a foreign key of its own.
#guard refusal (grown [judgeVerdicts.insert ⟨1, true⟩]) ==
  some (.invalid (.wrongFact "records" "judgeVerdicts"))
#guard refusal (grown [premiseLinks.insert ⟨9, 1⟩]) ==
  some (.invalid (.orphan "records" "premiseLinks"))
#guard refusal (grown [records.insert ⟨5, .claim, "unsourced"⟩]) ==
  some (.invalid (.missing "claimSources" "record"))
#guard refusal (grown [gateVerdicts.insert ⟨3, true⟩]) ==
  some (.invalid (.overlap "records" "judgeVerdicts" "gateVerdicts"))
#guard refusal (grown [premiseLinks.insert ⟨2, 1⟩]) ==
  some (.invalid (.overlap "records" "premiseQuotes" "premiseLinks"))
#guard refusal (grown [records.insert ⟨5, .verdict, "of no one"⟩]) ==
  some (.invalid (.uncovered "records" ["judgeVerdicts", "gateVerdicts"]))
#guard refusal (grown [records.insert ⟨5, .premise, "bare"⟩, notes.insert ⟨5, "bare"⟩]) ==
  some (.invalid (.uncovered "records" ["premiseQuotes", "premiseLinks"]))
-- A subtype for several values, and one for a family of values: a note for a claim or a premise,
-- a body for a record of any tagged kind.
#guard refusal (grown [records.insert ⟨5, .tagged "memo", "a memo"⟩,
    taggedBodies.insert ⟨5, "remember"⟩, records.insert ⟨6, .tagged "aside", "an aside"⟩,
    taggedBodies.insert ⟨6, "by the way"⟩]) == none
#guard refusal (grown [notes.insert ⟨3, "on a verdict"⟩]) ==
  some (.invalid (.wrongFact "records" "notes"))
#guard refusal (grown [taggedBodies.insert ⟨1, "on a claim"⟩]) ==
  some (.invalid (.wrongFact "records" "taggedBodies"))
#guard refusal (grown [notes.insert ⟨9, "on nothing"⟩]) ==
  some (.invalid (.orphan "records" "notes"))
#guard refusal (grown [records.insert ⟨5, .premise, "unnoted"⟩, premiseQuotes.insert ⟨5, "as given"⟩]) ==
  some (.invalid (.uncovered "records" ["notes", "taggedBodies"]))
#guard refusal (grown [records.insert ⟨5, .tagged "memo", "a memo"⟩]) ==
  some (.invalid (.uncovered "records" ["notes", "taggedBodies"]))
#guard (staleSnapshot.map fun rows ↦ refusal (Db.load schema rows)) ==
  some (some (.staleIndex "books" "booksByAuthor"))

/-- Whether the database of `library` with `delta` appended has a new row of an owner that
`library` has. -/
def thawed (delta : List (Insert schema)) : Option (Option Thaw) := do
  let before ← library.toOption
  let after ← (grown delta).toOption
  return schema.thaw? before.rows after.rows

/-- Whether `library` with its snapshot changed by `change` has a new row of an owner that
`library` has. -/
def thawedBy (change : Library → Library) : Option (Option Thaw) :=
  library.toOption.map fun db ↦ schema.thaw? db.rows (change db.rows)

-- A new record with its rows, and new rows of the roots, keep every owner's rows frozen.
#guard thawed [] == some none
#guard thawed [records.insert ⟨5, .premise, "new"⟩, premiseQuotes.insert ⟨5, "as given"⟩,
  notes.insert ⟨5, "new"⟩, reviews.insert ⟨5, "Ada", true⟩, books.insert ⟨13, 1, "Later"⟩] ==
  some none
-- Refused: a new row of a record that existed, through a foreign key or as a subtype; a record
-- replaced; a row of a table only the loader writes.
-- Each diagnosis names the table, the row's key, and the owner table and key.
#guard thawed [reviews.insert ⟨1, "Ada", true⟩] ==
  some (some (.owned "reviews" "(1, \"Ada\")" "records" "1"))
#guard thawedBy (fun rows ↦ { rows with judgeVerdicts := rows.judgeVerdicts.insertIfNew ⟨4, true⟩ }) ==
  some (some (.owned "judgeVerdicts" "4" "records" "4"))
#guard thawedBy (fun rows ↦ { rows with
    records := ((Rows.ofList? [⟨1, .claim, "changed"⟩] : Except Record (Rows Record.seq)).toOption.getD {}) }) ==
  some (some (.owned "records" "1" "records" "1"))
#guard thawed [authors.insert ⟨4, "Edsger"⟩] == some (some (.loaded "authors" "4"))

/-- A books table that forgets what is inserted into it but still adds it to its index. -/
def careless : Table Library Book.id :=
  (Table.make "books" Library.books (fun snapshot _ ↦ snapshot) "id" Book.id).index
    "booksByAuthor" Library.booksByAuthor fun snapshot index ↦ { snapshot with booksByAuthor := index }

/-- A records table that, besides the record asked for, slips an author into the authors. -/
def smuggler : Table Library Record.seq :=
  Table.make "records" Library.records (fun snapshot next ↦
    { snapshot with records := next
                    authors := (snapshot.authors.insertIfNew ⟨77, "Smuggled"⟩) }) "seq" Record.seq

/-- A schema with broken tables, which the audit would refuse, to show that `append` checks
what the tables' functions did. -/
def broken : Schema Library where
  tables := tables% [authors, careless, smuggler]

instance : InSchema broken careless := ⟨⟨1, by decide⟩, by rfl⟩
instance : InSchema broken smuggler := ⟨⟨2, by decide⟩, by rfl⟩

open Lean Meta in
/- `broken` declared audited without the audit, through the private constructor, which only
meta code can reach. -/
run_meta do
  let schema := Lean.mkConst ``broken
  let type ← mkAppM ``Audited #[schema]
  let value ← mkAppOptM auditedConstructor #[none, schema]
  addDecl <| .thmDecl { name := `RelationsCheck.brokenAudited, levelParams := [], type, value }
  addInstance `RelationsCheck.brokenAudited .global (eval_prio default)

/-- `delta` appended to the empty database of `broken`. -/
def appendBroken (delta : List (Insert broken)) : Option Refusal :=
  match Db.load broken {} with
  | .ok empty => refusal (empty.append delta)
  | .error violation => some (.invalid violation)

/-- A books table whose primary key is named after the wrong column. -/
def mislabelledBooks : Table Library Book.id :=
  Table.make "books" Library.books (fun snapshot value ↦ { snapshot with books := value }) "author"
    Book.id

/-- A schema of that table, which the audit would refuse for its missing tables, declared audited
without the audit, to show that the description checks the names it gives. -/
def mislabelled : Schema Library where
  tables := tables% [mislabelledBooks]

open Lean Meta in
run_meta do
  let schema := Lean.mkConst ``mislabelled
  let type ← mkAppM ``Audited #[schema]
  let value ← mkAppOptM auditedConstructor #[none, schema]
  addDecl <| .thmDecl { name := `RelationsCheck.mislabelledAudited, levelParams := [], type, value }
  addInstance `RelationsCheck.mislabelledAudited .global (eval_prio default)

/-- error: the primary key of books is not (author) -/
#guard_msgs in
#describe_schema Library mislabelled

/-- A row with a nested structure, keyed by a path through it. -/
structure Wrapped where
  inner : Author
  deriving @[expose] DecidableEq, Repr

structure Nest where
  wrapped : Rows fun (value : Wrapped) ↦ value.inner.id := {}

/-- A table whose primary key names a nested path rather than a top-level column. -/
def nestedWrapped : Table Nest fun (value : Wrapped) ↦ value.inner.id :=
  Table.make "wrapped" Nest.wrapped (fun snapshot value ↦ { snapshot with wrapped := value })
    "inner.id" fun value ↦ value.inner.id

/-- A schema of that table, declared audited without the audit. -/
def nested : Schema Nest where
  tables := tables% [nestedWrapped]

open Lean Meta in
run_meta do
  let schema := Lean.mkConst ``nested
  let type ← mkAppM ``Audited #[schema]
  let value ← mkAppOptM auditedConstructor #[none, schema]
  addDecl <| .thmDecl { name := `RelationsCheck.nestedAudited, levelParams := [], type, value }
  addInstance `RelationsCheck.nestedAudited .global (eval_prio default)

/-- error: the primary key of wrapped names inner.id, which is not a column of its rows -/
#guard_msgs in
#describe_schema Nest nested

-- The lost row is reported as lost, not as the stale index it leaves behind.
#guard appendBroken [careless.insert ⟨13, 1, "Dropped"⟩] == some (.lost "books")
#guard appendBroken [smuggler.insert ⟨5, .claim, "carrier"⟩] == some (.extra "authors")

/-- Runs `query` on `library`. -/
def ask {Result : Type} (query : Library → Result) : Option Result :=
  library.toOption.map fun db ↦ query db.rows

-- Queries: through an index, an antijoin, a join, the first and latest rows by a column, counts.
#guard ask (fun rows ↦ ((rows.booksByAuthor.lookup rows.books 1).project Book.title).sortedBy? id) ==
  some (some #["Notes", "Sketch"])
#guard ask (fun rows ↦ ((rows.edgesBySource.lookup rows.edges 1).project Edge.target).sortedBy? id) ==
  some (some #[3, 4])
#guard ask (fun rows ↦ ((Relation.antijoin (fun author book ↦ author.id == book.author)
    rows.authors.toRelation rows.books.toRelation).project Author.name).sortedBy? id) ==
  some (some #["Barbara"])
#guard ask (fun rows ↦ ((Relation.antijoinOn Author.id Book.author rows.authors.toRelation
    rows.books.toRelation).project Author.name).sortedBy? id) == some (some #["Barbara"])
#guard ask (fun rows ↦ ((Relation.semijoinOn Author.id Book.author rows.authors.toRelation
    rows.books.toRelation).project Author.name).sortedBy? id) == some (some #["Ada", "Grace"])
#guard ask (fun rows ↦ ((Relation.joinOn Edge.target Record.seq rows.edges.toRelation
    (rows.records.toRelation.select (·.kind == .verdict))).project (·.1.position)).sortedBy? id) ==
  some (some #[0, 1, 2])
#guard ask (fun rows ↦ (rows.edges.toRelation.maxBy Edge.position).the?) ==
  some (some ⟨2, 1, 4, .judgedBy⟩)
#guard ask (fun rows ↦ (rows.edges.toRelation.minBy Edge.position).the?) ==
  some (some ⟨0, 1, 3, .judgedBy⟩)
#guard ask (fun rows ↦ ((rows.edges.toRelation.minBy Edge.source).project Edge.position).sortedBy? id) ==
  some (some #[0, 2])
-- The latest edge from each source.
#guard ask (fun rows ↦ ((rows.edges.toRelation.maxByGroup Edge.source Edge.position).project
    Edge.position).sortedBy? id) == some (some #[1, 2])
#guard ask (fun rows ↦ (rows.books.count, rows.books.toRelation.count)) == some (3, 3)
-- A projection keeps a value for every row; `distinct` keeps each value once.
#guard ask (fun rows ↦ ((rows.books.toRelation.project Book.author).count,
    (rows.books.toRelation.project Book.author).distinct.count)) == some (3, 2)
-- A sum over a projection counts every row, also those with the same value.
#guard ask (fun rows ↦ (rows.books.toRelation.project Book.author).reduce .nat id) == some 4
#guard ask (fun rows ↦ rows.records.maxKey?) == some (some 4)
-- `distinct` removes repetition through a tree where the rows have a tree order.
example : (inferInstance : Relation.Dedup Nat) = Relation.Dedup.ofTreeOrd := rfl
-- A repeated row shares its own key, so a column with a repeated value is no key, even after a
-- projection to that column.
#guard ask (fun rows ↦ ((rows.books.toRelation.project Book.author).sortedBy? id).isSome) ==
  some false
#guard ask (fun rows ↦ (rows.books.toRelation.project Book.author).distinct.sortedBy? id) ==
  some (some #[1, 2])
-- Reachability: around a cycle and back, from a repeated seed, and from a seed no edge leaves.
#guard (Relation.reach (Relation.ofList [(1, 2), (2, 3), (3, 1), (4, 5)]) (Relation.ofList [1])).sortedBy?
  id == some #[1, 2, 3]
#guard (Relation.reach (Relation.ofList [(1, 2), (2, 3), (3, 1), (4, 5)]) (Relation.ofList [4, 4])).sortedBy?
  id == some #[4, 5]
#guard (Relation.reach (Relation.ofList ([] : List (Nat × Nat))) (Relation.ofList [7])).sortedBy? id ==
  some #[7]
-- Grouping: the books of each author, the number of books per author, and every title again as
-- the union of the groups.
#guard ask (fun rows ↦ ((rows.books.toRelation.groupBy Book.author).project fun (author, books) ↦
    (author, (books.project Book.title).sortedBy? id)).sortedBy? Prod.fst) ==
  some (some #[(1, some #["Notes", "Sketch"]), (2, some #["Compilers"])])
#guard ask (fun rows ↦ (rows.books.toRelation.aggregateBy Book.author .nat fun _ ↦ 1).sortedBy?
    Prod.fst) == some (some #[(1, 2), (2, 1)])
-- The greatest number of books by one author: a count per author, then the maximum.
#guard ask (fun rows ↦ (rows.books.toRelation.aggregateBy Book.author .nat fun _ ↦ 1).reduce .max (·.2)) ==
  some 2
#guard ask (fun rows ↦ (((rows.books.toRelation.groupBy Book.author).bind Prod.snd).project
    Book.title).sortedBy? id) == some (some #["Compilers", "Notes", "Sketch"])
-- A union keeps a row that both sides have twice, and a relation with a repeated row has no key,
-- not even the identity.
#guard ((Relation.ofList [1, 2]) ∪ (Relation.ofList [2, 3])).count == 4
#guard ((Relation.ofList [1, 2]) ∪ (Relation.ofList [2, 3])).multiplicity 2 == 2
#guard ((Relation.ofList [1, 2]) ∪ (Relation.ofList [2, 3])).keyed id == false
#guard ((Relation.ofList [1, 2]) ∪ (Relation.ofList [2, 3])).distinct.keyed id == true
/-- A row with equality but no order. -/
structure Shade where
  name : String
  deriving @[expose] DecidableEq

-- Rows with equality but no order lose their repetition by comparing pairs.
#guard ((Relation.ofList [(⟨"red"⟩ : Shade), ⟨"red"⟩, ⟨"blue"⟩]).distinct).count == 2
-- A column that is not a key gives no order.
#guard ask (fun rows ↦ (rows.books.toRelation.sortedBy? Book.author).isSome) == some false

-- The database before an append stays usable and keeps its rows.
#guard (library.toOption.bind fun db ↦ (db.append [books.insert ⟨13, 3, "Later"⟩]).toOption.map
    fun next ↦ (db.rows.books.count, next.next.rows.books.count)) == some (3, 4)

/-- A step that appends two deltas in turn.  Its type says that it returns a database grown from
the one it was given, keeping every row of it: it cannot start again from `Db.load`. -/
def twoAppends (db : Db schema) : Except Refusal db.Grown := do
  let first ← (Db.Grown.refl db).append [authors.insert ⟨4, "Edsger"⟩]
  first.append [books.insert ⟨13, 4, "Notes on structured programming"⟩]

#guard (do return (← twoAppends (← library)).next.rows.books.count : Except Refusal Nat).toOption ==
  some 4

section CompositeKeys

open scoped Relational.CompositeKeys

/-- A row keyed by a pair, ordered lexicographically once the scope is open. -/
structure Mark where
  record : Nat
  ordinal : Nat
  deriving @[expose] DecidableEq, Repr

#guard ((Rows.ofList? [⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 5⟩] :
    Except Mark (Rows fun (mark : Mark) ↦ (mark.record, mark.ordinal))).toOption.bind
      (·.maxKey?)) == some (1, 2)

end CompositeKeys

/-- Relations are equal whatever the order of the list they came from: no query can tell these
apart.  A repeated row is told apart: it counts twice. -/
example : Relation.ofList [1, 2, 1] = Relation.ofList [2, 1, 1] :=
  Relation.sound (List.Perm.swap 2 1 [1])

example : Relation.ofList [1, 2] ≠ Relation.ofList [2, 1, 1] := fun same ↦ by
  have := congrArg Relation.count same
  simp at this

/-! Schemas whose owners the audit refuses: a table that declares none, an owner column that
neither a foreign key nor a subtyping ties to the owner, an owner that owns no rows, owners in a
cycle, a subtype declared a root and a root whose primary key refers to a table that owns rows; a
primary key whose name is not its columns; and what the audit accepts, an owner column outside the
primary key and an owner that is itself owned. -/

structure Item where
  id : Nat
  deriving @[expose] DecidableEq, Repr

structure ItemNote where
  id : Nat
  item : Nat
  deriving @[expose] DecidableEq, Repr

namespace OwnerMissing

structure Store where
  items : Rows Item.id := {}

def items := table% Store.items (id)

def schema : Schema Store where
  tables := tables% [items]

/-- error: RelationsCheck.OwnerMissing.items declares no owner of its rows: root%, owner% or loaded% -/
#guard_msgs in
#audit_schema Store schema

end OwnerMissing

/-! Notes keyed by their own id, each of an item: the owner column is outside the primary key,
which `Frozen` does not need, since a note that exists stays and no new one may have its key. -/
namespace OwnerOffKey

structure Store where
  items : Rows Item.id := {}
  notes : Rows ItemNote.id := {}

def items := table% Store.items (id)
  root%

def notes := table% Store.notes (id)
  references% item → items
  owner% item → items

def schema : Schema Store where
  tables := tables% [items, notes]

#audit_schema Store schema

def store (items : List Item) (notes : List ItemNote) : Store :=
  { items := (Rows.ofList? items).toOption.getD {}, notes := (Rows.ofList? notes).toOption.getD {} }

#guard schema.thaw? (store [⟨1⟩] [⟨1, 1⟩]) (store [⟨1⟩, ⟨2⟩] [⟨1, 1⟩, ⟨2, 2⟩]) == none
#guard schema.thaw? (store [⟨1⟩] [⟨1, 1⟩]) (store [⟨1⟩] [⟨1, 1⟩, ⟨2, 1⟩]) ==
  some (.owned "notes" "2" "items" "1")

end OwnerOffKey

structure NoteTag where
  note : Nat
  tag : String
  deriving @[expose] DecidableEq, Repr

/-! Three levels of ownership: items, notes of an item with keys of their own, and tags of a note,
keyed by the note and the tag.  A tag belongs to a note, not to the item, and is frozen with it: a
new tag of an old note is refused, a new tag of a new note of a new item is not. -/
namespace OwnerChain

structure Store where
  items : Rows Item.id := {}
  notes : Rows ItemNote.id := {}
  tags : Rows (fun (tag : NoteTag) ↦ (tag.note, tag.tag)) := {}

def items := table% Store.items (id)
  root%

def notes := table% Store.notes (id)
  references% item → items
  owner% item → items

def tags := table% Store.tags (note, tag)
  references% note → notes
  owner% note → notes

def schema : Schema Store where
  tables := tables% [items, notes, tags]

#audit_schema Store schema

def store (items : List Item) (notes : List ItemNote) (tags : List NoteTag) : Store :=
  { items := (Rows.ofList? items).toOption.getD {}, notes := (Rows.ofList? notes).toOption.getD {}
    tags := (Rows.ofList? tags).toOption.getD {} }

def before : Store := store [⟨1⟩] [⟨10, 1⟩] [⟨10, "old"⟩]

#guard schema.thaw? before (store [⟨1⟩, ⟨2⟩] [⟨10, 1⟩, ⟨20, 2⟩] [⟨10, "old"⟩, ⟨20, "new"⟩]) ==
  none
#guard schema.thaw? before (store [⟨1⟩] [⟨10, 1⟩] [⟨10, "old"⟩, ⟨10, "late"⟩]) ==
  some (.owned "tags" "(10, \"late\")" "notes" "10")
#guard schema.thaw? before (store [⟨1⟩] [⟨10, 1⟩, ⟨11, 1⟩] [⟨10, "old"⟩, ⟨11, "new"⟩]) ==
  some (.owned "notes" "11" "items" "1")

end OwnerChain

/-! The tags declared a root instead: their key holds a foreign key into the notes, which own
rows, so a new tag of an old note would pass as a new root. -/
namespace RootOfOwned

structure Store where
  items : Rows Item.id := {}
  notes : Rows ItemNote.id := {}
  tags : Rows (fun (tag : NoteTag) ↦ (tag.note, tag.tag)) := {}

def items := table% Store.items (id)
  root%

def notes := table% Store.notes (id)
  references% item → items
  owner% item → items

def tags := table% Store.tags (note, tag)
  references% note → notes
  root%

def schema : Schema Store where
  tables := tables% [items, notes, tags]

/-- error: RelationsCheck.RootOfOwned.tags declares root%, but the column note of its primary key is a foreign key into
RelationsCheck.RootOfOwned.notes, which owns rows (root% or owner%), whose rows its rows belong to: owner% -/
#guard_msgs in
#audit_schema Store schema

end RootOfOwned

/-! Two tables each owned by the other: following the owners never reaches a root, so new rows of
both would pass together with no new root row.  `rightAhead` is the table `right` as seen before
it is defined, so that `left` can name it. -/
namespace OwnerCycle

structure Store where
  left : Rows ItemNote.id := {}
  right : Rows ItemNote.id := {}

def rightAhead := table% Store.right (id)
  root%

def left := table% Store.left (id)
  references% item → rightAhead
  owner% item → rightAhead

def right := table% Store.right (id)
  references% item → left
  owner% item → left

def schema : Schema Store where
  tables := tables% [left, right]

/-- error: following the owners from RelationsCheck.OwnerCycle.left runs in a cycle: RelationsCheck.OwnerCycle.left →
RelationsCheck.OwnerCycle.right → RelationsCheck.OwnerCycle.left -/
#guard_msgs in
#audit_schema Store schema

end OwnerCycle

namespace OwnerUnreferenced

structure Store where
  items : Rows Item.id := {}
  notes : Rows ItemNote.item := {}

def items := table% Store.items (id)
  root%

def notes := table% Store.notes (item)
  owner% item → items

def schema : Schema Store where
  tables := tables% [items, notes]

/-- error: the owner column item of RelationsCheck.OwnerUnreferenced.notes is neither a foreign key into items nor the
primary key of a subtype of it -/
#guard_msgs in
#audit_schema Store schema

end OwnerUnreferenced

namespace OwnerNotRoot

structure Store where
  items : Rows Item.id := {}
  notes : Rows ItemNote.item := {}

def items := table% Store.items (id)
  loaded%

def notes := table% Store.notes (item)
  references% item → items
  owner% item → items

def schema : Schema Store where
  tables := tables% [items, notes]

/-- error: the owner items of the rows of RelationsCheck.OwnerNotRoot.notes owns no rows (root% or owner%) -/
#guard_msgs in
#audit_schema Store schema

end OwnerNotRoot

structure Part where
  item : Nat
  name : String
  deriving @[expose] DecidableEq, Repr

/-! A subtype of a root declared a root: a new row of an old item would pass as a new root. -/
namespace RootSubtype

structure Store where
  items : Rows Item.id := {}
  details : Rows ItemNote.id := {}

def items := table% Store.items (id)
  root%

def details := table% Store.details (id)
  root%

def schema : Schema Store where
  tables := tables% [items, details]
  subtypings := [subtypes% items (id) [details ↦ family% fun _ ↦ true]]

/-- error: RelationsCheck.RootSubtype.details declares root%, but it is a subtype of RelationsCheck.RootSubtype.items,
whose rows its rows belong to: owner% -/
#guard_msgs in
#audit_schema Store schema

end RootSubtype

/-! A root whose primary key holds a foreign key into a root: its rows belong to the items. -/
namespace RootOfRoot

structure Store where
  items : Rows Item.id := {}
  parts : Rows (fun (part : Part) ↦ (part.item, part.name)) := {}

def items := table% Store.items (id)
  root%

def parts := table% Store.parts (item, name)
  references% item → items
  root%

def schema : Schema Store where
  tables := tables% [items, parts]

/-- error: RelationsCheck.RootOfRoot.parts declares root%, but the column item of its primary key is a foreign key into
RelationsCheck.RootOfRoot.items, which owns rows (root% or owner%), whose rows its rows belong to: owner% -/
#guard_msgs in
#audit_schema Store schema

end RootOfRoot

/-! A table whose primary key's name is not its columns: keyed by `id`, named by `item`. -/
namespace MisnamedKey

structure Store where
  items : Rows Item.id := {}
  notes : Rows ItemNote.id := {}

def items := table% Store.items (id)
  root%

def notes : Table Store ItemNote.id :=
  ((Table.make "notes" Store.notes (fun s r ↦ { s with notes := r }) "item" ItemNote.id).references
    "item" (·.item) items).owned "item" (·.item) items

def schema : Schema Store where
  tables := tables% [items, notes]

/-- error: the primary key of RelationsCheck.MisnamedKey.notes is not (item) -/
#guard_msgs in
#audit_schema Store schema

end MisnamedKey

/-! A table that declares no owner, in a schema that has not passed the audit, is never frozen. -/
namespace Undeclared

structure Store where
  items : Rows Item.id := {}

def items := table% Store.items (id)

def schema : Schema Store where
  tables := tables% [items]

#guard schema.thaw? {} {} == some (.undeclared "items")

end Undeclared

/-! An exhaustive subtyping: every record is in some member, so a record whose kind no member is
for is refused, where a covering subtyping would let it be in none. -/
namespace Exhaustive

inductive Shape where
  | dot
  | line
  | polygon (sides : Nat)
  deriving @[expose] DecidableEq, Repr

/-- Whether the shape is a polygon with more than three sides. -/
def Shape.many : Shape → Bool
  | .polygon (_ + 4) => true
  | _ => false

structure Figure where
  seq : Nat
  shape : Shape
  deriving @[expose] DecidableEq, Repr

structure Label where
  seq : Nat
  label : String
  deriving @[expose] DecidableEq, Repr

structure Store where
  figures : Rows Figure.seq := {}
  many : Rows Label.seq := {}
  few : Rows Label.seq := {}

def figures := table% Store.figures (seq)
  root%

def many := table% Store.many (seq)
  owner% seq → figures

def few := table% Store.few (seq)
  owner% seq → figures

def schema : Schema Store where
  tables := tables% [figures, many, few]
  subtypings := [subtypes% figures (shape) [many ↦ family% Shape.many,
    few ↦ values% [Shape.line, Shape.polygon 3]] exhaustive%]

#audit_schema Store schema
#describe_schema Store schema

-- A constructor with arguments is named as one without, by its short name.
#guard schema.description.subtypings == [
  { supertype := "figures", discriminator := "shape", coverage := .exhaustive
    members := [⟨"many", .predicate⟩, ⟨"few", .values ["line", "polygon 3"]⟩] }]

/-- What the database of the given rows refuses, if anything. -/
def load (figures : List Figure) (many few : List Label) : Option (Option Violation) := do
  let figures : Rows Figure.seq ← (Rows.ofList? figures).toOption
  let many : Rows Label.seq ← (Rows.ofList? many).toOption
  let few : Rows Label.seq ← (Rows.ofList? few).toOption
  return refusal (Db.load schema { figures, many, few })

#guard load [⟨1, .polygon 5⟩, ⟨2, .polygon 3⟩, ⟨3, .line⟩] [⟨1, "pentagon"⟩]
  [⟨2, "triangle"⟩, ⟨3, "segment"⟩] == some none
-- A polygon of four sides must be in `many` and a triangle in `few`; a dot or a polygon of two
-- sides, which no member is for, can be in none, and is refused.
#guard load [⟨1, .polygon 4⟩] [] [] == some (some (.uncovered "figures" ["many", "few"]))
#guard load [⟨1, .polygon 3⟩] [] [] == some (some (.uncovered "figures" ["many", "few"]))
#guard load [⟨1, .dot⟩] [] [] == some (some (.uncovered "figures" ["many", "few"]))
#guard load [⟨1, .polygon 2⟩] [] [⟨1, "digon"⟩] == some (some (.wrongFact "figures" "few"))

end Exhaustive

/-! The table command (`Relational/TableCommand.lean`): a schema declared with it, in a structure and one
that extends it, passes the audit with its tables in field order, whatever order the structures'
tables were declared in, and each refusal of the command names what it refuses, where it is.  With
`positions := true`, `#guard_msgs` prints a message's line relative to its own, and a line before
it as `+0`: what tells there that an error is at a clause's column, not at `table_defs%`, is the
column. -/
namespace Command

/-- A shelf of a room. -/
table% shelves : Shelf (id) in Rooms
  root%
where
  id : Nat
  label : String
  deriving @[expose] DecidableEq, Repr

/-- The numbers in use, a table whose primary key is the whole row. -/
table% numbers : Nat (*) in Building
  loaded%

/-- A place on a shelf. -/
table% places : Place (shelf, position) in Rooms
  /-- Every place is on a shelf. -/
  references% shelf → shelves
  owner% shelf → shelves
where
  shelf : Nat
  position : Nat
  deriving @[expose] DecidableEq, Repr

table_rows% Rooms

/-- The rooms and the numbers in use. -/
table_rows% Building extends Rooms

table_defs% Building

def schema : Schema Building where
  tables := declared_tables% Building

#audit_schema Building schema

#guard schema.tables.map (·.table.name) == ["shelves", "places", "numbers"]

/-! A table given a setter that does not write its group, defined by hand where `table_defs%` would
have given it the one `table_rows%` declares: the audit writes the group's setter out itself, rather
than comparing the table's with the declared one, so it refuses this one. -/
namespace BadSetter

table% racks : Rack (id) in Hall
  root%
where
  id : Nat
  deriving @[expose] DecidableEq

table_rows% Hall

def racks := table% Hall.racks (id) set% (fun (hall : Hall) _ ↦ hall)
  root%

def schema : Schema Hall where
  tables := tables% [racks]

/-- error: RelationsCheck.Command.BadSetter.racks does not replace the field racks -/
#guard_msgs in
#audit_schema Hall schema

end BadSetter

/-- error: a table shelves is declared already -/
#guard_msgs in
table% shelves : Shelf (id) in Halls
  root%

/-- error: Rooms is declared already (table_rows%): a table in it is declared before it -/
#guard_msgs in
table% late : Shelf (id) in Rooms
  root%

/-- error: a table of a row type declared elsewhere takes its doc comment before table% -/
#guard_msgs in
table% annotated : Shelf (id) in Halls
  /-- A doc comment after the header, for a row structure the table does not declare. -/
  root%

/--
@ +1:24...30
error: the row type RelationsCheck.Command.Shelf has no column number
-/
#guard_msgs (positions := true) in
table% unkeyed : Shelf (number) in Halls
  root%

/-- error: Building is declared already -/
#guard_msgs in
table_rows% Building

/-- error: no table is declared in Halls -/
#guard_msgs in
table_rows% Halls

/-- error: the tables of Rooms are defined already -/
#guard_msgs in
table_defs% Building

table% halls : Hall (id) in Wings
  root%
where
  id : Nat
  deriving @[expose] DecidableEq

table% doors : Door (id) in Wings
  owner% id → halls
where
  id : Nat
  deriving @[expose] DecidableEq

table_rows% Wings

table_defs% Wings

-- A column a clause names that the row type does not have is reported at the column, as it is
-- when `table_defs%` elaborates the clauses `table%` recorded (a failed definition there would be
-- left behind with `sorry`, which the axiom audit refuses, so the term is checked here instead).
/--
@ +2:9...13
error: Invalid field `hall`: The environment does not contain `RelationsCheck.Command.Door.hall`, so it is not possible
to project the field `hall` from an expression
  row
of type `Door`
-/
#guard_msgs (error, drop info, positions := true) in
#check table% Wings.doors (id) set% Wings.set_doors
  owner% hall → halls

-- A table in a structure that no `table_rows%` declares fails the next `table_defs%` and
-- `declared_tables%`, rather than being left out.
table% lost : Shelf (id) in Lost
  root%

/-- error: the table lost is in Lost, which no table_rows% has declared -/
#guard_msgs in
table_defs% Wings

/-- error: the table lost is in Lost, which no table_rows% has declared -/
#guard_msgs in
example : List (AnyTable Building) := declared_tables% Building

table_rows% Lost

end Command

end RelationsCheck
