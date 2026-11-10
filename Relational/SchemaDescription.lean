module

public import Lean.Data.Json
public import Lean.ToExpr
public import Lean.Elab.Deriving.ToExpr
public import Lean.Elab.Deriving.FromToJson

public section

/-! The description of a schema, as data: every table with its columns (the fields of its row
structure and their Lean types), primary key, further unique keys, foreign keys with the
restriction on their parent rows (a list of values, a constant relation of allowed parents, or a
predicate, which the description can only name as opaque), mandatory participations, indexes and
who owns its rows;
every subtyping, with its supertype, discriminating column, members and their values (listed, or
for a family of values an opaque predicate), and which supertype rows must be in one of them;
and every constant
relation of allowed parents, with its rows.  `#describe_schema` (`Relational/SchemaDescribe.lean`)
builds it from a schema that passed the schema audit, when the module that declares the schema is
built, and `SchemaDescription.write` writes it as JSON. -/

namespace Relational

open Lean

/-- A column of a table: a field of its row structure, own or inherited, and the name of its Lean
type. -/
structure ColumnDescription where
  name : String
  type : String
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

/-- The parent rows that a foreign key lets a child row refer to: any (`any`), those whose column
`column` has one of `values` (`facts`), those whose value of `parentColumn` makes, with the child
row's value of `childColumn` and the endpoint `endpoint`, a row of the constant relation named
`relation` (`allowance`), or those that an opaque predicate of the child and the parent row
accepts (`predicate`). -/
inductive RestrictionDescription where
  | any
  | facts (column : String) (values : List String)
  | allowance (childColumn relation endpoint parentColumn : String)
  | predicate
  deriving @[expose] DecidableEq, Repr, ToExpr

instance : ToJson RestrictionDescription where
  toJson
    | .any => Json.mkObj [("kind", "any")]
    | .facts column values =>
      Json.mkObj [("kind", "facts"), ("column", column), ("values", toJson values)]
    | .allowance childColumn relation endpoint parentColumn =>
      Json.mkObj [("kind", "allowance"), ("childColumn", childColumn), ("relation", relation),
        ("endpoint", endpoint), ("parentColumn", parentColumn)]
    | .predicate => Json.mkObj [("kind", "opaque predicate")]

/-- A foreign key: the column, the parent table whose primary key it matches, and the parent rows
it may match. -/
structure ForeignKeyDescription where
  column : String
  parent : String
  restriction : RestrictionDescription := .any
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

/-- The parent rows that a mandatory participation covers: all of them, or those that an opaque
predicate accepts. -/
inductive ScopeDescription where
  | all
  | predicate
  deriving @[expose] DecidableEq, Repr, ToExpr

instance : ToJson ScopeDescription where
  toJson
    | .all => "all"
    | .predicate => "opaque predicate"

/-- A mandatory participation: every parent row in `scope` has a row of the table whose column
`column` matches its primary key. -/
structure ParticipationDescription where
  column : String
  parent : String
  scope : ScopeDescription := .all
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

/-- An index of a table, by one of its columns. -/
structure IndexDescription where
  name : String
  column : String
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

/-- Who owns a table's rows: each row itself, operations appending them (`root`); the row of the
table `table`, a root or itself owned, whose primary key is the row's value of `column` (`owned`);
or no operation, only the loader writing the table (`loaded`). -/
inductive OwnerDescription where
  | root
  | owned (column table : String)
  | loaded
  deriving @[expose] DecidableEq, Repr, ToExpr

instance : ToJson OwnerDescription where
  toJson
    | .root => Json.mkObj [("kind", "root")]
    | .owned column table => Json.mkObj [("kind", "owned"), ("column", column), ("table", table)]
    | .loaded => Json.mkObj [("kind", "loaded")]

/-- A table: its name, columns, primary key, further unique keys, foreign keys, mandatory
participations, indexes and the owner of its rows.  A key lists its columns; a key of the whole
row lists them all. -/
structure TableDescription where
  name : String
  columns : List ColumnDescription
  primaryKey : List String
  uniqueKeys : List (List String) := []
  foreignKeys : List ForeignKeyDescription := []
  mandatory : List ParticipationDescription := []
  indexes : List IndexDescription := []
  owner : OwnerDescription
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

/-- The values of the supertype's discriminating column that a subtype table is for: those listed
(`values`), or those that an opaque predicate accepts (`predicate`). -/
inductive FactSetDescription where
  | values (values : List String)
  | predicate
  deriving @[expose] DecidableEq, Repr, ToExpr

instance : ToJson FactSetDescription where
  toJson
    | .values values => Json.mkObj [("kind", "values"), ("values", toJson values)]
    | .predicate => Json.mkObj [("kind", "opaque predicate")]

/-- A subtype table of a subtyping and the values of the supertype's discriminating column for its
rows. -/
structure SubtypeDescription where
  table : String
  facts : FactSetDescription
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

/-- Which supertype rows a subtyping requires to be in one of its members: none, those with a
value of some member (`covering`), or every one (`exhaustive`). -/
inductive CoverageDescription where
  | none
  | covering
  | exhaustive
  deriving @[expose] DecidableEq, Repr, ToExpr

instance : ToJson CoverageDescription where
  toJson
    | .none => "none"
    | .covering => "covering"
    | .exhaustive => "exhaustive"

/-- A subtyping: the supertype table, its discriminating column, the subtype tables, and which
supertype rows must be in one of them. -/
structure SubtypingDescription where
  supertype : String
  discriminator : String
  members : List SubtypeDescription
  coverage : CoverageDescription
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

/-- A row of a constant relation of allowed parents. -/
structure AllowanceRowDescription where
  child : String
  endpoint : String
  parent : String
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

/-- A constant relation of allowed parents: its name, the Lean types of its three columns, and its
rows. -/
structure AllowanceDescription where
  name : String
  childType : String
  endpointType : String
  parentType : String
  rows : List AllowanceRowDescription
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

/-- A schema: the snapshot structure, its tables in field order, its subtypings and the constant
relations its foreign keys use. -/
structure SchemaDescription where
  snapshot : String
  tables : List TableDescription
  subtypings : List SubtypingDescription := []
  allowances : List AllowanceDescription := []
  deriving @[expose] DecidableEq, Repr, ToJson, ToExpr

namespace SchemaDescription

/-- The table named `name`. -/
def table? (description : SchemaDescription) (name : String) : Option TableDescription :=
  description.tables.find? (·.name == name)

/-- The description as JSON text. -/
def render (description : SchemaDescription) : String :=
  (toJson description).pretty

/-- Writes the description as JSON to the file named by the only argument, or to standard output
without one, as the `main` of an executable that describes a schema. -/
def write (description : SchemaDescription) : List String → IO UInt32
  | [] => do
    IO.println description.render
    return 0
  | [path] => do
    IO.FS.writeFile path (description.render ++ "\n")
    return 0
  | _ => do
    IO.eprintln "expected at most one argument: the file to write the description to"
    return 2

end SchemaDescription

end Relational
