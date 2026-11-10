module

public import Relational.Rows
public import Relational.Place

-- `#audit_schema` and `#describe_schema` (Relational/SchemaAudit.lean, Relational/SchemaDescribe.lean) read a schema by
-- reducing its tables while the module that declares them elaborates, so the bodies here stay exposed; and the
-- builders of tables, subtypings and their members name the private constructors that keep those values to what
-- made them.
set_option backward.privateInPublic true -- principles: ignore[lean:private-in-public] builders use private constructors
set_option backward.privateInPublic.warn false

@[expose] public section -- principles: ignore[lean:expose-section] #audit_schema reduces schemas built here

namespace Relational

/-! Table definitions over a snapshot, a structure with one `Rows` field per table and one `Index`
field per index.  The type of a `Rows` field fixes the table's primary key, which is unique by
construction; a `Table` adds further unique keys, foreign keys, mandatory participations and the
indexes to maintain, in the manner of SQL `CREATE TABLE` statements.  A foreign key may be
restricted, for a column that refers to a supertype table, to some parent rows, as data where data
can state which (`Restriction`): those whose discriminating column has one of some values, or those
whose value makes, with the child row's value and the key's endpoint, a row of a constant relation
of the schema (`Allowance`); and otherwise those that a predicate of the child and the parent row
accepts.  A mandatory participation requires every row of a parent table, or every row of it that a
predicate accepts, to be referred to by a row of the table.  A `Subtyping` names, for each subtype
table of a supertype, the values of the supertype's discriminating column that its rows have (a
list of values, or a family that a predicate accepts, such as every value of one constructor), and
says that every row of a subtype has the key of a supertype row with one of its values, that the
subtype tables share no key, where it is declared covering, that every supertype row with a
value of some subtype is in one of them and, where it is declared exhaustive, that every supertype
row is in one of them, whatever its value.  Every table also says who owns its rows (`Ownership`):
each row itself, in a root table such as the records; a row of another table, a root or itself
owned, through a column that refers to it; or nobody, for a table only the loader writes; so that a
check can refuse a new row of an owner that already existed (`Table.Frozen`).  Each constraint has a proposition, a
check proved to decide it, and a diagnosis; the schema that collects them, with `Valid` and `Extends`,
is in `Relational/Database.lean`.
-/

/-- A further uniqueness constraint: no two rows share the value of `key`.  `holds` decides it;
it is built where the key type is concrete, so that it is compiled for that type. -/
structure UniqueKey (Row : Type) where
  private mk ::
  name : String
  Key : Type
  key : Row → Key
  holds : Relation Row → Bool
  holds_iff : ∀ rows, holds rows = true ↔ rows.Keyed key

/-- A constant relation of allowed parents, for a foreign key whose allowed parent rows depend on
the child row through a finite mapping.  A row `(child, endpoint, parent)` says that a child row
whose discriminating column has the value `child` may refer, through the foreign key at
`endpoint`, to a parent row whose discriminating column has the value `parent`: for the edges,
the edge's fact, the end of the edge, and a fact that the record at that end may have.  It belongs
to the schema, not to the snapshot, and the schema's description lists it under `name`.

It is for a table that holds several kinds of fact, such as one table of all relations: there a
foreign key alone accepts a parent of any kind, where one table per kind of fact would type it
directly, and the allowance restores that typing as data.  A child with a parent of a kind it may
not have is then refused when it is appended. -/
structure Allowance (Child Endpoint Parent : Type) where
  name : String
  rows : List (Child × Endpoint × Parent)

namespace Allowance

variable {Child Endpoint Parent : Type}

/-- The rows as a relation, for the propositions. -/
def toRelation (allowance : Allowance Child Endpoint Parent) :
    Relation (Child × Endpoint × Parent) :=
  Relation.ofList allowance.rows

/-- The pairs of a child and a parent value that the relation allows at `endpoint`. -/
def pairs [DecidableEq Endpoint] (allowance : Allowance Child Endpoint Parent)
    (endpoint : Endpoint) : List (Child × Parent) :=
  allowance.rows.filterMap fun (child, at_, parent) ↦
    if at_ = endpoint then some (child, parent) else none

theorem mem_pairs [DecidableEq Endpoint] {allowance : Allowance Child Endpoint Parent}
    {endpoint : Endpoint} {child : Child} {parent : Parent} :
    (child, parent) ∈ allowance.pairs endpoint ↔
      (child, endpoint, parent) ∈ allowance.toRelation := by
  simp only [pairs, toRelation, Relation.mem_ofList, List.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨child', at_, parent', member, found⟩
    split at found
    · rename_i same
      cases found
      exact same ▸ member
    · cases found
  · intro member
    exact ⟨child, endpoint, parent, member, by simp⟩

end Allowance

/-- Which parent rows a foreign key lets a child row refer to, as data where data can state it:
any parent row (`any`); those whose column `column`, read by `fact`, has one of `values`
(`facts`); those whose value of the column `parentColumn`, read by `fact`, makes with the child
row's value of its column `childColumn` and the foreign key's `endpoint` a row of the constant
relation `relation` (`allowance`); or, for a rule that data cannot state, those that a predicate of
the child and the parent row accepts (`predicate`), which the schema description can only name as
such. -/
inductive Restriction (Row Parent : Type) : Type 1 where
  | any
  | facts (column : String) {Fact : Type} [DecidableEq Fact] (fact : Parent → Fact)
      (values : List Fact)
  | allowance (childColumn : String) {Child Endpoint Fact : Type} [DecidableEq Child]
      [Hashable Child] [DecidableEq Endpoint] [DecidableEq Fact] [Hashable Fact]
      (child : Row → Child) (relation : Allowance Child Endpoint Fact) (endpoint : Endpoint)
      (parentColumn : String) (fact : Parent → Fact)
  | predicate (accepts : Row → Parent → Bool)

namespace Restriction

variable {Row Parent : Type}

/-- The child row `row` may refer to the parent row `parent`. -/
def Allows : Restriction Row Parent → Row → Parent → Prop
  | any, _, _ => True
  | facts _ fact values, _, parent => fact parent ∈ values
  | allowance _ child relation endpoint _ fact, row, parent =>
    (child row, endpoint, fact parent) ∈ relation.toRelation
  | predicate accepts, row, parent => accepts row parent = true

/-- `Allows`, decided: a scan of the values for `facts`, and for `allowance` a lookup in a hash set
of the pairs that the relation allows at the endpoint.  The compiler takes the row and the parent
as arguments of this function, so a call builds the hash set anew; `prepare` builds it once. -/
def allows : Restriction Row Parent → Row → Parent → Bool
  | any => fun _ _ ↦ true
  | facts _ fact values => fun _ parent ↦ values.contains (fact parent)
  | allowance _ child relation endpoint _ fact =>
    let known := Std.HashSet.ofList (relation.pairs endpoint)
    fun row parent ↦ known.contains (child row, fact parent)
  | predicate accepts => accepts

theorem allows_iff {restriction : Restriction Row Parent} {row : Row} {parent : Parent} :
    restriction.allows row parent = true ↔ restriction.Allows row parent := by
  cases restriction with
  | any => simp [allows, Allows]
  | facts column fact values => simp [allows, Allows]
  | allowance childColumn child relation endpoint parentColumn fact =>
    simp only [allows, Allows, Std.HashSet.contains_ofList, List.contains_iff_mem]
    exact Allowance.mem_pairs
  | predicate accepts => rfl

/-- A restriction ready to check child rows: `accepts` is `allows`, inside a structure so that the
compiler cannot take the rows as arguments of `prepare`, and the hash set of an allowance is built
once, when `prepare` is called. -/
structure Prepared (Row Parent : Type) where
  accepts : Row → Parent → Bool

/-- The restriction, ready to check child rows, as a foreign key keeps it. -/
@[noinline] def prepare : Restriction Row Parent → Prepared Row Parent
  | any => ⟨fun _ _ ↦ true⟩
  | facts _ fact values => ⟨fun _ parent ↦ values.contains (fact parent)⟩
  | allowance _ child relation endpoint _ fact =>
    let known := Std.HashSet.ofList (relation.pairs endpoint)
    ⟨fun row parent ↦ known.contains (child row, fact parent)⟩
  | predicate accepts => ⟨accepts⟩

theorem prepare_accepts {restriction : Restriction Row Parent} :
    restriction.prepare.accepts = restriction.allows := by
  cases restriction <;> rfl

end Restriction

/-- A column of `Row` that must match the primary key of a row of the parent table `parentName`
that `allowed` accepts for the child row; `allowed` is the compiled form of `restriction`.
`present` decides the match with any parent row and `holds` the match with an allowed one; both
are built where the types are concrete. -/
structure ForeignKey (Snapshot Row : Type) where
  private mk ::
  column : String
  parentName : String
  Parent : Type
  Key : Type
  reference : Row → Key
  parents : Snapshot → Relation Parent
  primary : Parent → Key
  /-- The place of the row a key names, where the parent's keys have places (`PlaceKey`). -/
  place : Snapshot → Key → Option Place
  restriction : Restriction Row Parent
  allowed : Row → Parent → Bool
  allowed_iff : ∀ child parent, allowed child parent = true ↔ restriction.Allows child parent
  present : Relation Row → Snapshot → Bool
  present_iff : ∀ children rows,
    present children rows = true ↔ Relation.References children reference (parents rows) primary
  holds : Relation Row → Snapshot → Bool
  holds_iff : ∀ children rows, holds children rows = true ↔
    ∀ child ∈ children, ∃ parent ∈ parents rows, allowed child parent = true ∧
      primary parent = reference child

/-- `holds` decides the foreign key as its restriction states it, as data where data can: for an
allowance relation, every child row refers to a parent row whose value, with the child row's value
and the key's endpoint, is a row of the relation. -/
theorem ForeignKey.holds_iff_allows {Snapshot Row : Type}
    (foreign : ForeignKey Snapshot Row) (children : Relation Row) (rows : Snapshot) :
    foreign.holds children rows = true ↔ ∀ child ∈ children, ∃ parent ∈ foreign.parents rows,
      foreign.restriction.Allows child parent ∧
        foreign.primary parent = foreign.reference child := by
  rw [foreign.holds_iff]
  exact forall_congr' fun child ↦ imp_congr_right fun _ ↦ exists_congr fun parent ↦
    and_congr_right fun _ ↦ and_congr_left' (foreign.allowed_iff child parent)

/-- A mandatory participation: every row of the parent table `parentName` that `scope` accepts has
a row of the table whose column `column` matches its primary key.  `holds` decides it, built where
the types are concrete. -/
structure Participation (Snapshot Row : Type) where
  private mk ::
  column : String
  parentName : String
  Parent : Type
  Key : Type
  reference : Row → Key
  parents : Snapshot → Relation Parent
  primary : Parent → Key
  scope : Parent → Bool
  holds : Relation Row → Snapshot → Bool
  holds_iff : ∀ children rows, holds children rows = true ↔
    ∀ parent ∈ parents rows, scope parent = true → ∃ child ∈ children,
      reference child = primary parent

/-- An index of a table with primary key `key`, kept in a field of the snapshot. -/
structure TableIndex (Snapshot : Type) {Row Key : Type} [TreeOrd Key] (key : Row → Key) where
  private mk ::
  name : String
  Column : Type
  [order : TreeOrd Column]
  column : Row → Column
  get : Snapshot → Index key column
  set : Snapshot → Index key column → Snapshot
  agrees : Index key column → Rows key → Bool
  agrees_iff : ∀ index rows, agrees index rows = true ↔ index.Agrees rows

attribute [instance] TableIndex.order

/-- The owner of every row of a table: the row of the table `ownerName` whose primary key is the
row's value of `column`.  `owns` decides whether a snapshot has that owner, built where the types
are concrete, and `render` gives an owner's key for diagnostics, as the snapshots that may hold
it name it. -/
structure Owner (Snapshot Row : Type) where
  private mk ::
  column : String
  ownerName : String
  Parent : Type
  Key : Type
  reference : Row → Key
  parents : Snapshot → Relation Parent
  primary : Parent → Key
  /-- The place of the owner a key names, where the owner's keys have places (`PlaceKey`). -/
  place : Snapshot → Key → Option Place
  render : List Snapshot → Key → String
  owns : Snapshot → Key → Bool
  owns_iff : ∀ rows wanted, owns rows wanted = true ↔ ∃ parent ∈ parents rows, primary parent = wanted

/-- Who adds the rows of a table, for the check that the rows of an owner that already exists
never change in number (`Table.Frozen`): an operation, each row its own owner (`root`), as the
records and relations are; an operation, each row belonging to a row of another table (`owned`),
a root or itself owned, as the rows that state something about a record, or about such a row, do; or only the loader,
from a store, never an operation (`loaded`), as constant tables are.
A table that declares none (`undeclared`) is refused by the schema audit, and no check takes its
rows as frozen. -/
inductive Ownership (Snapshot Row : Type) : Type 1 where
  | undeclared
  | root
  | owned (owner : Owner Snapshot Row)
  | loaded

/-- Why the rows of a snapshot `next` are not those of `previous` with rows appended only for new
owners (`Table.Frozen`), each key written as its table writes it in diagnostics. -/
inductive Thaw where
  /-- A row of `table` with primary key `rowKey`, which `previous` lacks, belongs to the row of the
  table `owner` with primary key `ownerKey`, which `previous` has; for a root table, `owner`
  is the table itself and `ownerKey` is `rowKey`. -/
  | owned (table rowKey owner ownerKey : String)
  /-- `table`, which only the loader writes, has a row with primary key `rowKey` that `previous`
  lacks. -/
  | loaded (table rowKey : String)
  /-- `table` declares no owner of its rows. -/
  | undeclared (table : String)
  deriving @[expose] DecidableEq, Repr

/-- How diagnostics write a key of type `Key`, given the snapshots that may hold the row it is the
key of, first those to look in first: as `Repr` writes it unless a schema says otherwise, as one
whose keys carry nothing readable does, to name a row by a column of it instead.  A pair is
written as `Repr` writes a tuple, each part as its type is. -/
class RenderKey (Snapshot Key : Type) where
  render : List Snapshot → Key → String

instance (priority := low) {Snapshot Key : Type} [Repr Key] : RenderKey Snapshot Key :=
  ⟨fun _ key ↦ reprStr key⟩

instance {Snapshot First Rest : Type} [RenderKey Snapshot First] [ReprTuple Rest] :
    RenderKey Snapshot (First × Rest) :=
  ⟨fun rows (first, rest) ↦ "(" ++ ", ".intercalate
    (RenderKey.render rows first :: (reprTuple rest []).reverse.map toString) ++ ")"⟩

/-- The place of the row a key of type `Key` names in a log that only grows, its position counting
from 1, looked up in a snapshot: as a record of a store has the place it was written at.  None
where the row has no place, as for every key type a schema gives no other instance for. -/
class PlaceKey (Snapshot Key : Type) where
  place? : Snapshot → Key → Option Place

instance (priority := low) {Snapshot Key : Type} : PlaceKey Snapshot Key := ⟨fun _ _ ↦ none⟩

/-- One table of a snapshot: the field holding its rows and the function that replaces them,
its primary key's name and how its keys are written in diagnostics, further unique keys, foreign
keys, mandatory participations, indexes and who owns its rows.  Tables, keys, foreign keys, participations, indexes and
owners are built only by `make`, `unique`, `references`, `mandatory`, `index`, `root`, `owned` and `loaded`, so that
every check is the compiled form of its proposition. -/
structure Table (Snapshot : Type) {Row Key : Type} [TreeOrd Key] (key : Row → Key) where
  private mk ::
  name : String
  primaryName : String
  renderKey : List Snapshot → Key → String
  /-- The place of the row a key names, where the keys have places (`PlaceKey`). -/
  placeOf : Snapshot → Key → Option Place
  rows : Snapshot → Rows key
  set : Snapshot → Rows key → Snapshot
  uniqueKeys : List (UniqueKey Row) := []
  foreignKeys : List (ForeignKey Snapshot Row) := []
  participations : List (Participation Snapshot Row) := []
  indexes : List (TableIndex Snapshot key) := []
  ownership : Ownership Snapshot Row := .undeclared

namespace Table

variable {Snapshot Row Key : Type} [TreeOrd Key]
  {key : Row → Key}

/-- The table read by `rows` and replaced by `set`, with no constraints beyond its primary key.
`primary` must be the key in the type of the rows; it is passed as written so that the
diagnostics name its columns (which the schema audit checks), and diagnostics give a key as
`RenderKey` writes it. -/
@[inline] def make [RenderKey Snapshot Key] [PlaceKey Snapshot Key] (name : String) (rows : Snapshot → Rows key)
    (set : Snapshot → Rows key → Snapshot) (primaryName : String) (primary : Row → Key)
    (_primary : key = primary := by rfl) : Table Snapshot key :=
  -- every field given: the defaults of a structure with a private constructor are not found when
  -- the body is public ("Not a definition or theorem: uniqueKeys._default")
  { name, primaryName, renderKey := RenderKey.render, placeOf := PlaceKey.place?, rows, set, uniqueKeys := [],
    foreignKeys := [], participations := [], indexes := [], ownership := .undeclared }

/-- Adds the constraint `UNIQUE (name)`. -/
@[inline] def unique (table : Table Snapshot key) (name : String)
    {Other : Type} [DecidableEq Other] [Hashable Other] (other : Row → Other) :
    Table Snapshot key :=
  { table with uniqueKeys := table.uniqueKeys ++ [{
      name, Key := Other, key := other, holds := fun rows ↦ rows.keyed other
      holds_iff := fun _ ↦ Relation.keyed_iff }] }

/-- A lookup by primary key finds a row that `accept` accepts exactly when one has that key. -/
private theorem lookup_iff {Parent ParentKey : Type} [TreeOrd ParentKey] {parentKey : Parent → ParentKey}
    (parents : Rows parentKey) (accept : Parent → Bool) (wanted : ParentKey) :
    (match parents.find? wanted with
      | some parent => accept parent
      | none => false) = true ↔
      ∃ parent ∈ parents.toRelation, accept parent = true ∧ parentKey parent = wanted := by
  constructor
  · intro holds
    cases found : parents.find? wanted with
    | none => simp [found] at holds
    | some parent =>
      simp only [found] at holds
      obtain ⟨member, same⟩ := Rows.find?_eq_some.mp found
      exact ⟨parent, Rows.mem_toRelation.mpr member, holds, same⟩
  · rintro ⟨parent, member, accepted, rfl⟩
    rw [Rows.find?_eq_some.mpr ⟨Rows.mem_toRelation.mp member, rfl⟩]
    exact accepted

/-- Adds the constraint `column REFERENCES parent`, restricted to the parent rows that
`restriction` allows for the child row: the kinds or fact types the column may refer to, which may
depend on the child row's own columns. -/
@[inline] def references {Parent ParentKey : Type} [TreeOrd ParentKey]
    {parentKey : Parent → ParentKey} (table : Table Snapshot key)
    (column : String) (reference : Row → ParentKey) (parent : Table Snapshot parentKey)
    (restriction : Restriction Row Parent := .any) : Table Snapshot key :=
  let check (accept : Row → Parent → Bool) (children : Relation Row) (rows : Snapshot) : Bool :=
    children.all fun child ↦
      match (parent.rows rows).find? (reference child) with
      | some found => accept child found
      | none => false
  let allowed := restriction.prepare.accepts
  { table with foreignKeys := table.foreignKeys ++ [{
      column, parentName := parent.name, Parent, Key := ParentKey, reference
      parents := fun rows ↦ (parent.rows rows).toRelation
      primary := parentKey, place := parent.placeOf, restriction, allowed
      allowed_iff := fun _ _ ↦ by
        simp only [allowed, Restriction.prepare_accepts]
        exact Restriction.allows_iff
      present := check fun _ _ ↦ true
      present_iff := fun children rows ↦ by
        -- in a module, `simp` no longer rewrites this body's match with `lookup_iff`; `exact` closes
        -- it up to unfolding
        simp only [check, Relation.all_iff, Relation.References]
        exact forall_congr' fun child ↦ imp_congr_right fun _ ↦
          (lookup_iff (parent.rows rows) (fun _ ↦ true) (reference child)).trans
            (by simp only [true_and])
      holds := check allowed
      holds_iff := fun children rows ↦ by
        simp only [check, Relation.all_iff]
        exact forall_congr' fun child ↦ imp_congr_right fun _ ↦
          lookup_iff (parent.rows rows) (allowed child) (reference child) }] }

/-- Adds the constraint that every row of `parent` that `scope` accepts has a row of the table
whose `reference` is its primary key: mandatory participation.  Checked by an antijoin through a
tree of the table's references. -/
@[inline] def mandatory {Parent ParentKey : Type} [TreeOrd ParentKey]
    {parentKey : Parent → ParentKey} (table : Table Snapshot key)
    (column : String) (reference : Row → ParentKey) (parent : Table Snapshot parentKey)
    (scope : Parent → Bool := fun _ ↦ true) : Table Snapshot key :=
  { table with participations := table.participations ++ [{
      column, parentName := parent.name, Parent, Key := ParentKey, reference
      parents := fun rows ↦ (parent.rows rows).toRelation
      primary := parentKey, scope
      holds := fun children rows ↦
        (Relation.antijoinOn parentKey reference ((parent.rows rows).toRelation.select scope)
          children).isEmpty
      holds_iff := fun children rows ↦ by
        simp only [Relation.isEmpty_iff, Relation.mem_antijoinOn, Relation.mem_select, not_and]
        constructor
        · intro holds parentRow member inScope
          refine Classical.byContradiction fun none ↦ holds parentRow ⟨member, inScope⟩ ?_
          exact fun child childMember same ↦ none ⟨child, childMember, same⟩
        · rintro holds parentRow ⟨member, inScope⟩ unmatched
          obtain ⟨child, childMember, same⟩ := holds parentRow member inScope
          exact unmatched child childMember same }] }

/-- Adds an index of the table by the column in the type of the field that `get` reads. -/
@[inline] def index {Column : Type} [TreeOrd Column] {column : Row → Column}
    (table : Table Snapshot key) (name : String)
    (get : Snapshot → Index key column) (set : Snapshot → Index key column → Snapshot) :
    Table Snapshot key :=
  { table with indexes := table.indexes ++ [{
      name, Column, column, get, set, agrees := Index.agrees
      agrees_iff := fun _ _ ↦ Index.agrees_iff }] }

/-- Declares the table a root of ownership: operations append its rows, each its own owner, and
other tables may declare their rows owned by its rows.  The schema audit refuses it for a subtype
and for a table a column of whose primary key is a foreign key into a table that owns rows, and
otherwise trusts it: it cannot tell a table whose rows are their own owners, such as a relation
with its own key, from a table of attributes of another table's rows with a surrogate key of its
own and the reference outside the key, and such a table declared a root lets a new row of an old
owner through `Frozen`.  A table that refers to another without a declared foreign key gives up
the owner check along with referential integrity: the audit sees no reference to refuse. -/
@[inline] def root (table : Table Snapshot key) : Table Snapshot key :=
  { table with ownership := .root }

/-- Declares that every row of the table belongs to the row of `owner`, a root table or itself
owned, whose primary key is the row's `reference`, read from the column `column`. -/
@[inline] def owned {Parent ParentKey : Type} [TreeOrd ParentKey] {parentKey : Parent → ParentKey}
    (table : Table Snapshot key)
    (column : String) (reference : Row → ParentKey) (owner : Table Snapshot parentKey) :
    Table Snapshot key :=
  { table with ownership := .owned {
      column, ownerName := owner.name, Parent, Key := ParentKey, reference
      parents := fun rows ↦ (owner.rows rows).toRelation, primary := parentKey
      place := owner.placeOf, render := owner.renderKey
      owns := fun rows wanted ↦ (owner.rows rows).contains wanted
      owns_iff := fun rows wanted ↦ by simp [Rows.contains_iff] } }

/-- Declares that only the loader writes the table: no operation adds a row to it. -/
@[inline] def loaded (table : Table Snapshot key) : Table Snapshot key :=
  { table with ownership := .loaded }

/-- No two rows share a further unique key; the primary key is unique by construction. -/
def Keyed (table : Table Snapshot key) (rows : Snapshot) : Prop :=
  ∀ unique ∈ table.uniqueKeys, (table.rows rows).toRelation.Keyed unique.key

/-- Every foreign key of every row matches a parent row that it may refer to. -/
def Referenced (table : Table Snapshot key) (rows : Snapshot) : Prop :=
  ∀ foreign ∈ table.foreignKeys, ∀ child ∈ (table.rows rows).toRelation,
    ∃ parent ∈ foreign.parents rows, foreign.allowed child parent = true ∧
      foreign.primary parent = foreign.reference child

/-- `Referenced`, stated through the foreign keys' restrictions. -/
theorem referenced_iff {table : Table Snapshot key} {rows : Snapshot} :
    table.Referenced rows ↔ ∀ foreign ∈ table.foreignKeys, ∀ child ∈ (table.rows rows).toRelation,
      ∃ parent ∈ foreign.parents rows, foreign.restriction.Allows child parent ∧
        foreign.primary parent = foreign.reference child :=
  forall_congr' fun foreign ↦ imp_congr_right fun _ ↦ forall_congr' fun child ↦
    imp_congr_right fun _ ↦ exists_congr fun parent ↦ and_congr_right fun _ ↦
      and_congr_left' (foreign.allowed_iff child parent)

/-- Every parent row in the scope of a mandatory participation has a row of the table that
refers to it. -/
def Participates (table : Table Snapshot key) (rows : Snapshot) : Prop :=
  ∀ participation ∈ table.participations, ∀ parent ∈ participation.parents rows,
    participation.scope parent = true → ∃ child ∈ (table.rows rows).toRelation,
      participation.reference child = participation.primary parent

/-- No row of the table in `next` that the table in `previous` lacks belongs to an owner that
`previous` has: for a root table, no new row has the primary key of a row of `previous`; for an
owned table, none belongs to a row of the owner table in `previous`; and a table only the loader
writes has no new row at all.  A table that declares no owner is never frozen, so that no table
the audit has not seen passes unchecked.  With `Schema.Extends`, rows are then only appended with
new owners: the rows of an owner that exists neither change nor grow in number.  Where the owner
is itself owned, a new row of a new owner row passes here, and the owner table's own `Frozen`
refuses that owner row if its owner is old, and so on up to a root.  The check is only as good as
the declarations: a table declared `root%` whose rows are in fact attributes of another table's
rows, with a key of their own, is not frozen with them (`Table.root`). -/
def Frozen (table : Table Snapshot key) (previous next : Snapshot) : Prop :=
  match table.ownership with
  | .undeclared => False
  | .root => ∀ row ∈ table.rows next, row ∉ table.rows previous →
      ¬ ∃ old ∈ table.rows previous, key old = key row
  | .owned owner => ∀ row ∈ table.rows next, row ∉ table.rows previous →
      ¬ ∃ parent ∈ owner.parents previous, owner.primary parent = owner.reference row
  | .loaded => (table.rows next).Included (table.rows previous)

/-- Every index agrees with the table's rows. -/
def Indexed (table : Table Snapshot key) (rows : Snapshot) : Prop :=
  ∀ index ∈ table.indexes, (index.get rows).Agrees (table.rows rows)

instance (unique : UniqueKey Row) (rows : Relation Row) : Decidable (rows.Keyed unique.key) :=
  decidable_of_iff _ (unique.holds_iff rows)

instance (index : TableIndex Snapshot key) (rows : Snapshot) (table : Rows key) :
    Decidable ((index.get rows).Agrees table) :=
  decidable_of_iff _ (index.agrees_iff (index.get rows) table)

instance (table : Table Snapshot key) (rows : Snapshot) : Decidable (table.Keyed rows) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

instance (table : Table Snapshot key) (rows : Snapshot) : Decidable (table.Referenced rows) :=
  decidable_of_iff (∀ foreign ∈ table.foreignKeys,
      foreign.holds (table.rows rows).toRelation rows = true)
    (forall_congr' fun foreign ↦ imp_congr_right fun _ ↦ foreign.holds_iff _ _)

instance (table : Table Snapshot key) (rows : Snapshot) : Decidable (table.Participates rows) :=
  decidable_of_iff (∀ participation ∈ table.participations,
      participation.holds (table.rows rows).toRelation rows = true)
    (forall_congr' fun participation ↦ imp_congr_right fun _ ↦ participation.holds_iff _ _)

instance (table : Table Snapshot key) (rows : Snapshot) : Decidable (table.Indexed rows) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The name of the first further unique key of `table` that two rows share, if any. -/
def duplicate? (table : Table Snapshot key) (rows : Snapshot) : Option String :=
  (table.uniqueKeys.find? fun unique ↦ !unique.holds (table.rows rows).toRelation).map (·.name)

/-- The first foreign key of `table` with a value that matches no parent row it may refer to, if
any, and whether every value of it matches some parent row. -/
def unmatched? (table : Table Snapshot key) (rows : Snapshot) :
    Option (ForeignKey Snapshot Row × Bool) :=
  (table.foreignKeys.find? fun foreign ↦ !foreign.holds (table.rows rows).toRelation rows).map
    fun foreign ↦ (foreign, foreign.present (table.rows rows).toRelation rows)

/-- The column of the first mandatory participation of `table` that a parent row lacks. -/
def unmet? (table : Table Snapshot key) (rows : Snapshot) : Option String :=
  (table.participations.find? fun participation ↦
    !participation.holds (table.rows rows).toRelation rows).map (·.column)

/-- The name of the first index of `table` that disagrees with its rows, if any. -/
def unindexed? (table : Table Snapshot key) (rows : Snapshot) : Option String :=
  (table.indexes.find? fun index ↦ !index.agrees (index.get rows) (table.rows rows)).map (·.name)

/-- Two rows of `table` share the further unique key named `name`. -/
def KeyShared (table : Table Snapshot key) (rows : Snapshot) (name : String) : Prop :=
  ∃ unique ∈ table.uniqueKeys, unique.name = name ∧ ¬ (table.rows rows).toRelation.Keyed unique.key

/-- A row of `table` whose value of `column` matches no parent row. -/
def ColumnDangles (table : Table Snapshot key) (rows : Snapshot) (column : String) : Prop :=
  ∃ foreign ∈ table.foreignKeys, foreign.column = column ∧ ∃ child ∈ table.rows rows,
    ¬ ∃ parent ∈ foreign.parents rows, foreign.primary parent = foreign.reference child

/-- A row of `table` whose value of `column` matches a parent row, but not one the row may
refer to. -/
def ColumnWrongKind (table : Table Snapshot key) (rows : Snapshot) (column : String) : Prop :=
  ∃ foreign ∈ table.foreignKeys, foreign.column = column ∧ ∃ child ∈ table.rows rows,
    (∃ parent ∈ foreign.parents rows, foreign.primary parent = foreign.reference child) ∧
    ¬ ∃ parent ∈ foreign.parents rows, foreign.allowed child parent = true ∧
      foreign.primary parent = foreign.reference child

/-- A parent row in the scope of the mandatory participation through `column` that no row of
`table` refers to. -/
def ColumnMissing (table : Table Snapshot key) (rows : Snapshot) (column : String) : Prop :=
  ∃ participation ∈ table.participations, participation.column = column ∧
    ∃ parent ∈ participation.parents rows, participation.scope parent = true ∧
      ¬ ∃ child ∈ table.rows rows, participation.reference child = participation.primary parent

/-- The index named `name` of `table` disagrees with its rows. -/
def IndexStale (table : Table Snapshot key) (rows : Snapshot) (name : String) : Prop :=
  ∃ index ∈ table.indexes, index.name = name ∧ ¬ (index.get rows).Agrees (table.rows rows)

theorem duplicate?_eq_some {table : Table Snapshot key} {rows : Snapshot} {name : String}
    (found : table.duplicate? rows = some name) : table.KeyShared rows name := by
  obtain ⟨unique, first, named⟩ := Option.map_eq_some_iff.mp found
  refine ⟨unique, List.mem_of_find?_eq_some first, named, fun keyed ↦ ?_⟩
  have := List.find?_some first
  simp [(unique.holds_iff _).2 keyed] at this

theorem duplicate?_eq_none {table : Table Snapshot key} {rows : Snapshot} :
    table.duplicate? rows = none ↔ table.Keyed rows := by
  rw [duplicate?, Option.map_eq_none_iff, List.find?_eq_none]
  refine forall_congr' fun unique ↦ imp_congr_right fun _ ↦ ?_
  rw [← unique.holds_iff]
  simp

/-- What `unmatched?` reports is a row whose reference matches no parent row, if some value of
the column matches none, and otherwise a row whose reference matches a parent row it may not
refer to. -/
theorem unmatched?_eq_some {table : Table Snapshot key} {rows : Snapshot}
    {foreign : ForeignKey Snapshot Row} {present : Bool}
    (found : table.unmatched? rows = some (foreign, present)) :
    (present = false → table.ColumnDangles rows foreign.column) ∧
      (present = true → table.ColumnWrongKind rows foreign.column) := by
  obtain ⟨first, firstFound, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  have member := List.mem_of_find?_eq_some firstFound
  have failing := List.find?_some firstFound
  simp only [Bool.not_eq_true'] at failing
  have unmatched : ¬ ∀ child ∈ (table.rows rows).toRelation, ∃ parent ∈ foreign.parents rows,
      foreign.allowed child parent = true ∧ foreign.primary parent = foreign.reference child :=
    fun holds ↦ by simp [(foreign.holds_iff _ _).mpr holds] at failing
  refine ⟨fun absent ↦ ?_, fun present ↦ ?_⟩
  · have : ¬ Relation.References (table.rows rows).toRelation foreign.reference
        (foreign.parents rows) foreign.primary :=
      fun referenced ↦ by simp [(foreign.present_iff _ _).mpr referenced] at absent
    simp only [Relation.References, Classical.not_forall] at this
    obtain ⟨child, childMember, none⟩ := this
    exact ⟨foreign, member, rfl, child, Rows.mem_toRelation.mp childMember, none⟩
  · have referenced := (foreign.present_iff _ _).mp present
    simp only [Classical.not_forall] at unmatched
    obtain ⟨child, childMember, none⟩ := unmatched
    exact ⟨foreign, member, rfl, child, Rows.mem_toRelation.mp childMember,
      referenced child childMember, none⟩

theorem unmatched?_eq_none {table : Table Snapshot key} {rows : Snapshot} :
    table.unmatched? rows = none ↔ table.Referenced rows := by
  rw [unmatched?, Option.map_eq_none_iff, List.find?_eq_none]
  refine forall_congr' fun foreign ↦ imp_congr_right fun _ ↦ ?_
  rw [← foreign.holds_iff]
  simp

theorem unmet?_eq_some {table : Table Snapshot key} {rows : Snapshot} {column : String}
    (found : table.unmet? rows = some column) : table.ColumnMissing rows column := by
  obtain ⟨participation, first, named⟩ := Option.map_eq_some_iff.mp found
  have failing := List.find?_some first
  simp only [Bool.not_eq_true'] at failing
  have unmet : ¬ ∀ parent ∈ participation.parents rows, participation.scope parent = true →
      ∃ child ∈ (table.rows rows).toRelation,
        participation.reference child = participation.primary parent :=
    fun holds ↦ by simp [(participation.holds_iff _ _).mpr holds] at failing
  simp only [Classical.not_forall] at unmet
  obtain ⟨parent, parentMember, inScope, none⟩ := unmet
  exact ⟨participation, List.mem_of_find?_eq_some first, named, parent, parentMember, inScope,
    fun ⟨child, childMember, same⟩ ↦ none ⟨child, Rows.mem_toRelation.mpr childMember, same⟩⟩

theorem unmet?_eq_none {table : Table Snapshot key} {rows : Snapshot} :
    table.unmet? rows = none ↔ table.Participates rows := by
  rw [unmet?, Option.map_eq_none_iff, List.find?_eq_none]
  refine forall_congr' fun participation ↦ imp_congr_right fun _ ↦ ?_
  rw [← participation.holds_iff]
  simp

theorem unindexed?_eq_some {table : Table Snapshot key} {rows : Snapshot} {name : String}
    (found : table.unindexed? rows = some name) : table.IndexStale rows name := by
  obtain ⟨index, first, named⟩ := Option.map_eq_some_iff.mp found
  refine ⟨index, List.mem_of_find?_eq_some first, named, fun agreeing ↦ ?_⟩
  have := List.find?_some first
  simp [(index.agrees_iff _ _).2 agreeing] at this

/-- What a thawed table holds: a row that `Frozen` refuses, by the table's name and the row's
primary key, and the owner the row belongs to; or a table that declares no owner. -/
def Thawed (table : Table Snapshot key) (previous next : Snapshot) : Thaw → Prop
  | .owned name rowKey owner ownerKey => name = table.name ∧ ∃ row ∈ table.rows next,
      row ∉ table.rows previous ∧ table.renderKey [previous, next] (key row) = rowKey ∧
      match table.ownership with
      | .root => owner = table.name ∧ ownerKey = rowKey ∧
          ∃ old ∈ table.rows previous, key old = key row
      | .owned found => owner = found.ownerName ∧
          found.render [previous] (found.reference row) = ownerKey ∧
          ∃ parent ∈ found.parents previous, found.primary parent = found.reference row
      | _ => False
  | .loaded name rowKey => name = table.name ∧ table.ownership = .loaded ∧
      ∃ row ∈ table.rows next, row ∉ table.rows previous ∧
        table.renderKey [previous, next] (key row) = rowKey
  | .undeclared name => name = table.name ∧ table.ownership = .undeclared

/-- A row of the table in `next` that `Frozen` refuses, with its owner, which of the refused rows
not said (`Rows.any?`: the table's keys may carry no order, as record and relation keys do not), by
a lookup of every row of the table in `next` in the table in `previous` and,
for one that is new, of its owner in the owner table in `previous`: in O(n log n) time for n rows
of the table, at once only where the table in `next` is the same object in memory as in
`previous` (`Rows.included`).  A table loaded anew from a store, as the store's growth check
loads the store after an operation, is not the same object even where its rows are, and pays the
lookups.  A row's key is written as `previous` or else `next` names it, and the owner of a row of
an owned table as `previous` does, as `thawIn?` writes them. -/
def thaw? [DecidableEq Row] (table : Table Snapshot key) (previous next : Snapshot) : Option Thaw :=
  match table.ownership with
  | .undeclared => some (.undeclared table.name)
  | .root => if (table.rows next).included (table.rows previous) then none else
      ((table.rows next).any? fun row ↦
          !decide (row ∈ table.rows previous) && (table.rows previous).contains (key row)).map
        fun row ↦ .owned table.name (table.renderKey [previous, next] (key row)) table.name
          (table.renderKey [previous, next] (key row))
  | .owned owner => if (table.rows next).included (table.rows previous) then none else
      ((table.rows next).any? fun row ↦
          !decide (row ∈ table.rows previous) && owner.owns previous (owner.reference row)).map
        fun row ↦ .owned table.name (table.renderKey [previous, next] (key row)) owner.ownerName
          (owner.render [previous] (owner.reference row))
  | .loaded => if (table.rows next).included (table.rows previous) then none else
      ((table.rows next).any? fun row ↦ !decide (row ∈ table.rows previous)).map fun row ↦
        .loaded table.name (table.renderKey [previous, next] (key row))

theorem thaw?_eq_none [DecidableEq Row] {table : Table Snapshot key} {previous next : Snapshot} :
    table.thaw? previous next = none ↔ table.Frozen previous next := by
  unfold thaw? Frozen
  split
  · simp
  · split
    · rename_i included
      simp only [true_iff]
      intro row member fresh
      exact absurd (Rows.included_iff.mp included row member) fresh
    · rw [Option.map_eq_none_iff, Rows.any?_eq_none]
      refine forall_congr' fun row ↦ imp_congr_right fun _ ↦ ?_
      by_cases old : row ∈ table.rows previous
      · simp [old]
      · simp only [old, decide_false, Bool.not_false, Bool.true_and, not_false_eq_true,
          forall_const, Bool.eq_false_iff, ne_eq, Rows.contains_iff, not_exists, not_and]
  · rename_i owner _
    split
    · rename_i included
      simp only [true_iff]
      intro row member fresh
      exact absurd (Rows.included_iff.mp included row member) fresh
    · rw [Option.map_eq_none_iff, Rows.any?_eq_none]
      refine forall_congr' fun row ↦ imp_congr_right fun _ ↦ ?_
      by_cases old : row ∈ table.rows previous
      · simp [old]
      · simp only [old, decide_false, Bool.not_false, Bool.true_and, not_false_eq_true,
          forall_const, Bool.eq_false_iff, ne_eq]
        constructor
        · intro absent owned
          exact absent ((owner.owns_iff previous _).mpr owned)
        · intro absent present
          exact absent ((owner.owns_iff previous _).mp present)
  · split
    · rename_i included
      simp only [true_iff]
      exact Rows.included_iff.mp included
    · rename_i excluded
      simp only [Option.map_eq_none_iff, Rows.any?_eq_none, Bool.not_eq_false',
        decide_eq_true_eq]
      constructor
      · intro holds
        exact Rows.included_iff.mp (by
          cases inc : (table.rows next).included (table.rows previous)
          · exact absurd (Rows.included_iff.mpr fun row member ↦ holds row member) (by simp [inc])
          · rfl)
      · intro included
        exact absurd (Rows.included_iff.mpr included) excluded

/-- What `thaw?` reports holds of the table, as `Thawed` says. -/
theorem thaw?_sound [DecidableEq Row] {table : Table Snapshot key} {previous next : Snapshot}
    {thaw : Thaw} (found : table.thaw? previous next = some thaw) :
    table.Thawed previous next thaw := by
  unfold thaw? at found
  split at found
  · rename_i same
    cases found
    exact ⟨rfl, same⟩
  · rename_i same
    split at found
    · cases found
    · obtain ⟨row, first, rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨member, accepted⟩ := Rows.any?_eq_some first
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Rows.contains_iff] at accepted
      refine ⟨rfl, row, member, accepted.1, rfl, ?_⟩
      rw [same]
      exact ⟨rfl, rfl, accepted.2⟩
  · rename_i owner same
    split at found
    · cases found
    · obtain ⟨row, first, rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨member, accepted⟩ := Rows.any?_eq_some first
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at accepted
      refine ⟨rfl, row, member, accepted.1, rfl, ?_⟩
      rw [same]
      exact ⟨rfl, rfl, (owner.owns_iff previous _).mp accepted.2⟩
  · rename_i same
    split at found
    · cases found
    · obtain ⟨row, first, rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨member, accepted⟩ := Rows.any?_eq_some first
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at accepted
      exact ⟨rfl, same, row, member, accepted, rfl⟩

instance [DecidableEq Row] (table : Table Snapshot key) (previous next : Snapshot) :
    Decidable (table.Frozen previous next) :=
  decidable_of_iff _ (Option.isNone_iff_eq_none.trans thaw?_eq_none)

/-- `thaw?` for a `next` whose rows are those of `previous` and of `delta`, looking only at the
rows of `delta`: a row of the table in `delta`, which of them not said (`Rows.any?`), that
`previous` lacks and `Frozen` refuses, with its owner, in O(d log n) time for d rows of the table
in `delta` and n in `previous`.  The rows of `next` that `previous` lacks are rows of `delta`, so
finding none means `Frozen` (`thawIn?_frozen`); and where `next` has exactly the rows of both,
they are the rows of `delta` that `previous` lacks, so the row found is one that `thaw?` may
find.  A row's key is written as `previous` or else `delta` names it, and the owner of a
row of an owned table as `previous` does. -/
def thawIn? [DecidableEq Row] (table : Table Snapshot key) (previous delta : Snapshot) :
    Option Thaw :=
  match table.ownership with
  | .undeclared => some (.undeclared table.name)
  | .root =>
    ((table.rows delta).any? fun row ↦
        !decide (row ∈ table.rows previous) && (table.rows previous).contains (key row)).map
      fun row ↦ .owned table.name (table.renderKey [previous, delta] (key row)) table.name
        (table.renderKey [previous, delta] (key row))
  | .owned owner =>
    ((table.rows delta).any? fun row ↦
        !decide (row ∈ table.rows previous) && owner.owns previous (owner.reference row)).map
      fun row ↦ .owned table.name (table.renderKey [previous, delta] (key row)) owner.ownerName
        (owner.render [previous] (owner.reference row))
  | .loaded =>
    ((table.rows delta).any? fun row ↦ !decide (row ∈ table.rows previous)).map fun row ↦
      .loaded table.name (table.renderKey [previous, delta] (key row))

/-- Where every row of `next` is a row of `previous` or of `delta`, `thawIn?` finding nothing in
`delta` means that `next` is frozen on `previous`. -/
theorem thawIn?_frozen [DecidableEq Row] {table : Table Snapshot key}
    {previous delta next : Snapshot}
    (split : ∀ row ∈ table.rows next, row ∈ table.rows previous ∨ row ∈ table.rows delta)
    (none : table.thawIn? previous delta = none) : table.Frozen previous next := by
  cases ownership : table.ownership with
  | undeclared => simp [thawIn?, ownership] at none
  | root =>
    simp only [thawIn?, ownership, Option.map_eq_none_iff, Rows.any?_eq_none] at none
    simp only [Frozen, ownership]
    intro row member fresh ⟨old, oldMember, same⟩
    have refused := none row ((split row member).resolve_left fresh)
    simp only [fresh, decide_false, Bool.not_false, Bool.true_and] at refused
    rw [Rows.contains_iff.mpr ⟨old, oldMember, same⟩] at refused
    cases refused
  | owned owner =>
    simp only [thawIn?, ownership, Option.map_eq_none_iff, Rows.any?_eq_none] at none
    simp only [Frozen, ownership]
    intro row member fresh owns
    have refused := none row ((split row member).resolve_left fresh)
    simp [fresh, (owner.owns_iff previous _).mpr owns] at refused
  | loaded =>
    simp only [thawIn?, ownership, Option.map_eq_none_iff, Rows.any?_eq_none] at none
    simp only [Frozen, ownership]
    intro row member
    refine Classical.byContradiction fun fresh ↦ ?_
    have refused := none row ((split row member).resolve_left fresh)
    simp [fresh] at refused

/-- A row of the table in `delta` that refers, by a foreign key other than the column its owner is
read from, to a row whose place is not below its owner's, which of them not said (`Rows.any?`): the
column, the owner's place and the place referred to, both looked up in `rows`.  None where the table
is not owned, or where the owner's or the parent's keys have no places (`PlaceKey`): a row is
written with its owner, and may refer only to what was written before it. -/
def forwardIn? (table : Table Snapshot key) (rows delta : Snapshot) : Option (String × Place × Place) :=
  match table.ownership with
  | .owned owner =>
    let forward (row : Row) : Option (String × Place × Place) := do
      let at_ ← owner.place rows (owner.reference row)
      table.foreignKeys.findSome? fun foreign ↦ do
        guard (foreign.column != owner.column)
        let place ← foreign.place rows (foreign.reference row)
        if place < at_ then none else some (foreign.column, at_, place)
    ((table.rows delta).any? fun row ↦ (forward row).isSome).bind forward
  | _ => none

theorem unindexed?_eq_none {table : Table Snapshot key} {rows : Snapshot} :
    table.unindexed? rows = none ↔ table.Indexed rows := by
  rw [unindexed?, Option.map_eq_none_iff, List.find?_eq_none]
  refine forall_congr' fun index ↦ imp_congr_right fun _ ↦ ?_
  rw [← index.agrees_iff]
  simp

end Table

/-- A table of any row and key type, so that all tables of a snapshot fit in one list. -/
structure AnyTable (Snapshot : Type) where
  {Row : Type}
  {Key : Type}
  [rowEq : DecidableEq Row]
  [order : TreeOrd Key]
  {key : Row → Key}
  table : Table Snapshot key

attribute [instance] AnyTable.rowEq AnyTable.order

instance {Snapshot Row Key : Type} [DecidableEq Row] [TreeOrd Key] {key : Row → Key} : CoeOut
    (Table Snapshot key) (AnyTable Snapshot) :=
  ⟨AnyTable.mk⟩

/-- The values of a supertype's discriminating column that a subtype table is for: those listed
(`values`), as data, or, for a set that no list states, those that a predicate accepts (`family`),
such as every value made by one constructor, whatever its arguments.  The schema description lists
the values, and can name a family only as an opaque predicate.  The schema audit refuses an empty
list and a list with a value twice, but cannot tell in general whether a family accepts any value
at all: a family that accepts none is a member that no row may be in, which nothing refuses. -/
inductive FactSet (Fact : Type) where
  | values (values : List Fact)
  | family (accepts : Fact → Bool)

namespace FactSet

variable {Fact : Type}

/-- `fact` is one of the values. -/
def Contains : FactSet Fact → Fact → Prop
  | values list, fact => fact ∈ list
  | family accepts, fact => accepts fact = true

/-- `Contains`, decided: a scan of the list, or the predicate. -/
def contains [DecidableEq Fact] : FactSet Fact → Fact → Bool
  | values list, fact => list.contains fact
  | family accepts, fact => accepts fact

theorem contains_iff [DecidableEq Fact] {facts : FactSet Fact} {fact : Fact} :
    facts.contains fact = true ↔ facts.Contains fact := by
  cases facts <;> simp [contains, Contains]

instance [DecidableEq Fact] (facts : FactSet Fact) (fact : Fact) : Decidable (facts.Contains fact) :=
  decidable_of_iff _ contains_iff

end FactSet

/-- A subtype table of a supertype whose primary key has type `Key`, for the supertype rows whose
discriminating column has one of the values `facts`: its keys, as a relation for the propositions
and in ascending order for the checks, and whether it has a key. -/
structure SubtypeMember (Snapshot Key Fact : Type) where
  private mk ::
  name : String
  facts : FactSet Fact
  keys : Snapshot → Relation Key
  keyList : Snapshot → List Key
  mem_keyList : ∀ rows primary, primary ∈ keyList rows ↔ primary ∈ keys rows
  has : Snapshot → Key → Bool
  has_iff : ∀ rows primary, has rows primary = true ↔ primary ∈ keys rows

/-- The table as the subtype table for the supertype rows with one of the values `facts`: its
primary keys, which are the keys of supertype rows. -/
@[inline] def SubtypeMember.of {Snapshot Row Key Fact : Type} [TreeOrd Key] {key : Row → Key}
    (table : Table Snapshot key) (facts : FactSet Fact) :
    SubtypeMember Snapshot Key Fact :=
  { name := table.name, facts, keys := fun rows ↦ (table.rows rows).toRelation.project key
    keyList := fun rows ↦ (table.rows rows).keysInAnyOrder
    mem_keyList := fun rows primary ↦ by simp [Rows.mem_keysInAnyOrder]
    has := fun rows primary ↦ (table.rows rows).contains primary
    has_iff := fun rows primary ↦ by simp [Rows.contains_iff] }

/-- Which supertype rows a subtyping requires to be in one of its members: none (`none`); those
with a value of some member (`covering`); or every one (`exhaustive`), so that a value outside all
members is refused. -/
inductive Coverage where
  | none
  | covering
  | exhaustive
  deriving @[expose] DecidableEq, Repr

/-- The subtype tables of one supertype table, each for the supertype rows with some values of the
supertype's discriminating column `fact` (a fact type, or a kind).  Every row of a member has the
key of a supertype row with one of the member's values (`Typed`), so that the member needs no
foreign key of its own to the supertype; no two members share a key (`Disjoint`); and where the
subtyping is covering, every supertype row with a value of some member is in one of them
(`Covered`), and so in exactly one; where it is exhaustive, every supertype row is, so that no
value lies outside all members.  Two members may share a value: a row with it is then in at
most one of them.  The same declaration serves a group of attribute tables keyed by a parent
table of which every parent row of the given values has exactly one, such as one table of the
texts of several fact types.  The schema audit requires `fact` to be a column of the supertype's
rows. -/
structure Subtyping (Snapshot : Type) where
  private mk ::
  supertype : AnyTable Snapshot
  Fact : Type
  [factEq : DecidableEq Fact]
  fact : supertype.Row → Fact
  members : List (SubtypeMember Snapshot supertype.Key Fact)
  coverage : Coverage

attribute [instance] Subtyping.factEq

namespace Subtyping

variable {Snapshot Key Fact : Type}

/-- The subtypes `members` of `supertype`, whose primary key they share, each for the supertype
rows with its values of the column `fact`, covering the supertype's rows as `coverage` says. -/
@[inline] def make {SuperRow : Type} [DecidableEq SuperRow] [DecidableEq Fact] [TreeOrd Key] {superKey : SuperRow → Key}
    (supertype : Table Snapshot superKey) (fact : SuperRow → Fact)
    (members : List (SubtypeMember Snapshot Key Fact)) (coverage : Coverage := .none) :
    Subtyping Snapshot :=
  { supertype := supertype, Fact, fact, members, coverage }

/-- The name of the supertype table. -/
def name (subtyping : Subtyping Snapshot) : String := subtyping.supertype.table.name

/-- Whether the supertype row `row` must be of some member: the subtyping is covering and some
member is for the row's fact, or it is exhaustive. -/
def inScope (subtyping : Subtyping Snapshot) (row : subtyping.supertype.Row) : Bool :=
  match subtyping.coverage with
  | .none => false
  | .covering => subtyping.members.any fun member ↦ member.facts.contains (subtyping.fact row)
  | .exhaustive => true

/-- The keys of the supertype rows that must be of some subtype. -/
def covered (subtyping : Subtyping Snapshot) (rows : Snapshot) : Relation subtyping.supertype.Key :=
  ((subtyping.supertype.table.rows rows).toRelation.select subtyping.inScope).project
    subtyping.supertype.key

/-- Every row of a member has the key of a supertype row with one of the member's facts. -/
def Typed (subtyping : Subtyping Snapshot) (rows : Snapshot) : Prop :=
  ∀ member ∈ subtyping.members, ∀ primary ∈ member.keys rows,
    ∃ parent ∈ subtyping.supertype.table.rows rows, subtyping.supertype.key parent = primary ∧
      member.facts.Contains (subtyping.fact parent)

/-- A row of the member named `name` has a key that no supertype row has. -/
def Orphaned (subtyping : Subtyping Snapshot) (rows : Snapshot) (name : String) : Prop :=
  ∃ member ∈ subtyping.members, member.name = name ∧ ∃ primary ∈ member.keys rows,
    ∀ parent ∈ subtyping.supertype.table.rows rows, subtyping.supertype.key parent ≠ primary

/-- A row of the member named `name` has the key of a supertype row of a fact not its own. -/
def Misfiled (subtyping : Subtyping Snapshot) (rows : Snapshot) (name : String) : Prop :=
  ∃ member ∈ subtyping.members, member.name = name ∧ ∃ primary ∈ member.keys rows,
    ∃ parent ∈ subtyping.supertype.table.rows rows, subtyping.supertype.key parent = primary ∧
      ¬ member.facts.Contains (subtyping.fact parent)

/-- Whether the supertype row with key `primary` is missing (`some false`) or of a fact not among
`member`'s (`some true`). -/
private def misfit (subtyping : Subtyping Snapshot) (rows : Snapshot)
    (member : SubtypeMember Snapshot subtyping.supertype.Key subtyping.Fact)
    (primary : subtyping.supertype.Key) : Option Bool :=
  match (subtyping.supertype.table.rows rows).find? primary with
  | some parent => if member.facts.Contains (subtyping.fact parent) then none else some true
  | none => some false

private theorem misfit_eq_none {subtyping : Subtyping Snapshot} {rows : Snapshot}
    {member : SubtypeMember Snapshot subtyping.supertype.Key subtyping.Fact}
    {primary : subtyping.supertype.Key} :
    subtyping.misfit rows member primary = none ↔
      ∃ parent ∈ subtyping.supertype.table.rows rows, subtyping.supertype.key parent = primary ∧
        member.facts.Contains (subtyping.fact parent) := by
  unfold misfit
  split
  · rename_i parent found
    obtain ⟨parentMember, parentKey⟩ := Rows.find?_eq_some.mp found
    constructor
    · intro none
      split at none
      · rename_i same
        exact ⟨parent, parentMember, parentKey, same⟩
      · cases none
    · rintro ⟨other, otherMember, otherKey, otherFact⟩
      cases Rows.key_injective otherMember parentMember (otherKey.trans parentKey.symm)
      simp [otherFact]
  · rename_i absent
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro parent parentMember parentKey _
    rw [Rows.find?_eq_some.mpr ⟨parentMember, parentKey⟩] at absent
    cases absent

private theorem misfit_eq_some {subtyping : Subtyping Snapshot} {rows : Snapshot}
    {member : SubtypeMember Snapshot subtyping.supertype.Key subtyping.Fact}
    {primary : subtyping.supertype.Key} {wrong : Bool}
    (found : subtyping.misfit rows member primary = some wrong) :
    (wrong = false →
      ∀ parent ∈ subtyping.supertype.table.rows rows, subtyping.supertype.key parent ≠ primary) ∧
    (wrong = true → ∃ parent ∈ subtyping.supertype.table.rows rows,
      subtyping.supertype.key parent = primary ∧ ¬ member.facts.Contains (subtyping.fact parent)) := by
  unfold misfit at found
  split at found
  · rename_i parent parentFound
    obtain ⟨parentMember, parentKey⟩ := Rows.find?_eq_some.mp parentFound
    split at found
    · cases found
    · rename_i differs
      cases found
      exact ⟨fun same ↦ (by cases same), fun _ ↦ ⟨parent, parentMember, parentKey, differs⟩⟩
  · rename_i absent
    cases found
    refine ⟨fun _ parent parentMember parentKey ↦ ?_, fun same ↦ by cases same⟩
    rw [Rows.find?_eq_some.mpr ⟨parentMember, parentKey⟩] at absent
    cases absent

/-- The first member, in list order, with a row whose key no supertype row has (`false`) or a
supertype row of another fact has (`true`): a lookup in the supertype's tree for every row of
every member.  A member's rows are looked at in an order not said (`Rows.keysInAnyOrder`), so where
it has misfits of both kinds, the flag is either. -/
def firstMisfit (subtyping : Subtyping Snapshot) (rows : Snapshot) : Option (String × Bool) :=
  subtyping.members.findSome? fun member ↦
    ((member.keyList rows).findSome? (subtyping.misfit rows member)).map (member.name, ·)

theorem firstMisfit_eq_none {subtyping : Subtyping Snapshot} {rows : Snapshot} :
    subtyping.firstMisfit rows = none ↔ subtyping.Typed rows := by
  simp only [firstMisfit, List.findSome?_eq_none_iff, Option.map_eq_none_iff, misfit_eq_none, Typed]
  refine forall_congr' fun member ↦ imp_congr_right fun _ ↦ ?_
  exact forall_congr' fun primary ↦ imp_congr_left (member.mem_keyList rows primary)

/-- What `firstMisfit` reports is a member with a row whose key no supertype row has, or one
whose supertype row is of another fact, as it says. -/
theorem firstMisfit_eq_some {subtyping : Subtyping Snapshot} {rows : Snapshot} {name : String}
    {wrong : Bool} (found : subtyping.firstMisfit rows = some (name, wrong)) :
    (wrong = false → subtyping.Orphaned rows name) ∧
      (wrong = true → subtyping.Misfiled rows name) := by
  obtain ⟨member, memberIn, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨verdict, misfitFound, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  obtain ⟨primary, inList, isMisfit⟩ := List.exists_of_findSome?_eq_some misfitFound
  have inKeys := (member.mem_keyList rows primary).mp inList
  obtain ⟨orphan, misfiled⟩ := misfit_eq_some isMisfit
  exact ⟨fun same ↦ ⟨member, memberIn, rfl, primary, inKeys, orphan same⟩,
    fun same ↦ ⟨member, memberIn, rfl, primary, inKeys, misfiled same⟩⟩

instance (subtyping : Subtyping Snapshot) (rows : Snapshot) : Decidable (subtyping.Typed rows) :=
  decidable_of_iff _ firstMisfit_eq_none

/-- No key of `first` is a key of `second`. -/
def Apart (first second : SubtypeMember Snapshot Key Fact) (rows : Snapshot) : Prop :=
  ∀ primary ∈ first.keys rows, primary ∉ second.keys rows

section Pass

variable [TreeOrd Key]

/-- `seen` with the keys `keys` added. -/
private def insertKeys (seen : Std.ExtTreeSet Key TreeOrd.cmp) (keys : List Key) :
    Std.ExtTreeSet Key TreeOrd.cmp :=
  keys.foldl (·.insert ·) seen

private theorem mem_insertKeys {primary : Key} :
    ∀ {seen : Std.ExtTreeSet Key TreeOrd.cmp} {keys : List Key},
      primary ∈ insertKeys seen keys ↔ primary ∈ seen ∨ primary ∈ keys
  | _, [] => by simp [insertKeys]
  | seen, first :: rest => by
    show primary ∈ insertKeys (seen.insert first) rest ↔ _
    rw [mem_insertKeys, Std.ExtTreeSet.mem_insert, List.mem_cons]
    constructor
    · rintro ((same | member) | later)
      · exact Or.inr (Or.inl (Std.LawfulEqCmp.eq_of_compare same).symm)
      · exact Or.inl member
      · exact Or.inr (Or.inr later)
    · rintro (member | rfl | later)
      · exact Or.inl (Or.inr member)
      · exact Or.inl (Or.inl Std.ReflCmp.compare_self)
      · exact Or.inr later

/-- The keys of all of `members`, in a balanced tree. -/
private def allKeys (rows : Snapshot) (members : List (SubtypeMember Snapshot Key Fact)) :
    Std.ExtTreeSet Key TreeOrd.cmp :=
  members.foldl (fun seen member ↦ insertKeys seen (member.keyList rows)) ∅

private theorem mem_allKeys {rows : Snapshot} {primary : Key} :
    ∀ {members : List (SubtypeMember Snapshot Key Fact)} {seen : Std.ExtTreeSet Key TreeOrd.cmp},
      primary ∈ members.foldl (fun seen member ↦ insertKeys seen (member.keyList rows)) seen ↔
        primary ∈ seen ∨ ∃ member ∈ members, primary ∈ member.keys rows
  | [], _ => by simp
  | member :: rest, seen => by
    rw [List.foldl_cons, mem_allKeys, mem_insertKeys, member.mem_keyList]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((inSeen | inMember) | later)
      · exact Or.inl inSeen
      · exact Or.inr (Or.inl inMember)
      · exact Or.inr (Or.inr later)
    · rintro (inSeen | inMember | later)
      · exact Or.inl (Or.inl inSeen)
      · exact Or.inl (Or.inr inMember)
      · exact Or.inr later

/-- The first member, in list order, with a key of an earlier member, with that earlier member:
one pass over the keys, collected in a balanced tree.  `seen` holds the keys of `earlier`, the
members already passed, latest first. -/
private def overlapFrom (rows : Snapshot) (seen : Std.ExtTreeSet Key TreeOrd.cmp)
    (earlier : List (SubtypeMember Snapshot Key Fact)) :
    List (SubtypeMember Snapshot Key Fact) → Option (String × String)
  | [] => none
  | member :: rest =>
    match (member.keyList rows).find? seen.contains with
    | some shared =>
      (earlier.find? fun owner ↦ owner.has rows shared).map fun owner ↦ (owner.name, member.name)
    | none => overlapFrom rows (insertKeys seen (member.keyList rows)) (member :: earlier) rest

private theorem overlapFrom_eq_none {rows : Snapshot} :
    ∀ {members earlier : List (SubtypeMember Snapshot Key Fact)} {seen : Std.ExtTreeSet Key TreeOrd.cmp},
      (∀ primary, primary ∈ seen ↔ ∃ member ∈ earlier, primary ∈ member.keys rows) →
      (overlapFrom rows seen earlier members = none ↔
        (∀ member ∈ members, ∀ before ∈ earlier, Apart before member rows) ∧
          members.Pairwise fun first second ↦ Apart first second rows)
  | [], _, _, _ => by simp [overlapFrom]
  | member :: rest, earlier, seen, holds => by
    unfold overlapFrom
    split
    · rename_i shared found
      have inMember := (member.mem_keyList rows shared).mp (List.mem_of_find?_eq_some found)
      have inSeen := List.find?_some found
      rw [← Std.ExtTreeSet.mem_iff_contains, holds] at inSeen
      obtain ⟨owner, ownerMember, inOwner⟩ := inSeen
      have : (earlier.find? fun owner ↦ owner.has rows shared).isSome := by
        rw [List.find?_isSome]
        exact ⟨owner, ownerMember, (owner.has_iff rows shared).mpr inOwner⟩
      obtain ⟨first, firstFound⟩ := Option.isSome_iff_exists.mp this
      simp only [firstFound, Option.map_some, reduceCtorEq, false_iff, not_and]
      intro apart
      exact absurd inMember (apart member List.mem_cons_self owner ownerMember shared inOwner)
    · rename_i absent
      have fresh : ∀ before ∈ earlier, Apart before member rows := by
        intro before beforeMember primary inBefore inMember
        have inSeen := (holds primary).mpr ⟨before, beforeMember, inBefore⟩
        have := List.find?_eq_none.mp absent primary ((member.mem_keyList rows primary).mpr inMember)
        simp [Std.ExtTreeSet.mem_iff_contains.mp inSeen] at this
      rw [overlapFrom_eq_none (fun primary ↦ by
        rw [mem_insertKeys, holds, member.mem_keyList]
        simp only [List.mem_cons, exists_eq_or_imp]
        exact or_comm)]
      simp only [List.mem_cons, forall_eq_or_imp, List.pairwise_cons]
      constructor
      · rintro ⟨later, pairwise⟩
        exact ⟨⟨fresh, fun other otherMember ↦ (later other otherMember).2⟩,
          fun other otherMember ↦ (later other otherMember).1, pairwise⟩
      · rintro ⟨⟨_, later⟩, first, pairwise⟩
        exact ⟨fun other otherMember ↦ ⟨first other otherMember, later other otherMember⟩,
          pairwise⟩

private theorem overlapFrom_eq_some {rows : Snapshot} {firstName secondName : String} :
    ∀ {members earlier : List (SubtypeMember Snapshot Key Fact)} {seen : Std.ExtTreeSet Key TreeOrd.cmp},
      overlapFrom rows seen earlier members = some (firstName, secondName) →
      ∃ first second, [first, second].Sublist (earlier.reverse ++ members) ∧
        first.name = firstName ∧ second.name = secondName ∧ ¬ Apart first second rows
  | [], _, _, found => by simp [overlapFrom] at found
  | member :: rest, earlier, seen, found => by
    unfold overlapFrom at found
    split at found
    · rename_i shared sharedFound
      obtain ⟨owner, ownerFound, same⟩ := Option.map_eq_some_iff.mp found
      cases same
      have inMember := (member.mem_keyList rows shared).mp (List.mem_of_find?_eq_some sharedFound)
      have ownerHas := List.find?_some ownerFound
      have inOwner := (owner.has_iff rows shared).mp ownerHas
      refine ⟨owner, member, ?_, rfl, rfl, fun apart ↦ apart shared inOwner inMember⟩
      have : owner ∈ earlier.reverse := List.mem_reverse.mpr (List.mem_of_find?_eq_some ownerFound)
      exact (List.singleton_sublist.mpr this).append (List.cons_sublist_cons.mpr (List.nil_sublist _))
    · obtain ⟨first, second, sublist, rest⟩ := overlapFrom_eq_some found
      refine ⟨first, second, ?_, rest⟩
      simpa using sublist

/-- The first two members, in list order, that share a key: one pass over all their keys, each
member's in an order not said (`Rows.keysInAnyOrder`), so where several pairs share keys, the pair
found is any of them. -/
def firstOverlap (rows : Snapshot) (members : List (SubtypeMember Snapshot Key Fact)) :
    Option (String × String) :=
  overlapFrom rows ∅ [] members

theorem firstOverlap_eq_none {rows : Snapshot} {members : List (SubtypeMember Snapshot Key Fact)} :
    firstOverlap rows members = none ↔ members.Pairwise fun first second ↦ Apart first second rows := by
  rw [firstOverlap, overlapFrom_eq_none (fun primary ↦ by simp)]
  simp

/-- What `firstOverlap` reports are two members that share a key, the first one listed before
the second, so two distinct members. -/
theorem firstOverlap_eq_some {rows : Snapshot} {members : List (SubtypeMember Snapshot Key Fact)}
    {firstName secondName : String} (found : firstOverlap rows members = some (firstName, secondName)) :
    ∃ first second, [first, second].Sublist members ∧ first.name = firstName ∧
      second.name = secondName ∧ ¬ Apart first second rows := by
  simpa using overlapFrom_eq_some found

end Pass

/-- No two subtype tables share a key. -/
def Disjoint (subtyping : Subtyping Snapshot) (rows : Snapshot) : Prop :=
  subtyping.members.Pairwise fun first second ↦ Apart first second rows

/-- Every supertype row in the scope of the subtyping is of some subtype. -/
def Covered (subtyping : Subtyping Snapshot) (rows : Snapshot) : Prop :=
  ∀ primary ∈ subtyping.covered rows, ∃ member ∈ subtyping.members, primary ∈ member.keys rows

instance (subtyping : Subtyping Snapshot) (rows : Snapshot) : Decidable (subtyping.Disjoint rows) :=
  decidable_of_iff _ firstOverlap_eq_none

/-- `Covered`, by looking the key of every supertype row up in a tree of all the members' keys,
in O((n + m) log m) time for n supertype rows and m member rows, and comparing the fact of a
supertype row that is of no member with the members' facts, in O(k) time for k members. -/
def coveredBy (subtyping : Subtyping Snapshot) (rows : Snapshot) : Bool :=
  let all := allKeys rows subtyping.members
  (subtyping.supertype.table.rows rows).toRelation.all fun row ↦
    all.contains (subtyping.supertype.key row) || !subtyping.inScope row

theorem coveredBy_iff {subtyping : Subtyping Snapshot} {rows : Snapshot} :
    subtyping.coveredBy rows = true ↔ subtyping.Covered rows := by
  simp only [coveredBy, Relation.all_iff, Bool.or_eq_true, Bool.not_eq_true',
    ← Std.ExtTreeSet.mem_iff_contains, allKeys, mem_allKeys, Std.ExtTreeSet.not_mem_empty,
    false_or, Covered, covered, Relation.mem_project, Relation.mem_select]
  constructor
  · rintro holds primary ⟨row, ⟨member, inside⟩, rfl⟩
    rcases holds row member with found | outside
    · exact found
    · simp [inside] at outside
  · intro holds row member
    by_cases inside : subtyping.inScope row = true
    · exact Or.inl (holds _ ⟨row, ⟨member, inside⟩, rfl⟩)
    · exact Or.inr (by simpa using inside)

instance (subtyping : Subtyping Snapshot) (rows : Snapshot) : Decidable (subtyping.Covered rows) :=
  decidable_of_iff _ coveredBy_iff

end Subtyping

/-! `table% Snapshot.questions (id)` is the table read from the field `questions` of the structure
`Snapshot`, its own or inherited, named after that field; `(id)` names the primary key, which must
be the one in the field's type `Rows`, and `(question, proposition)` a composite key (kept in the
lexicographic tree order of pairs, `TreeOrd.prod`).  `unique% (inquiry, ordinal)` adds a further
unique key, `references% inquiry → inquiries` a foreign key from column `inquiry` to the primary key
of table `inquiries` (`parent% inquiry → inquiries` declares both that foreign key and that the row
it refers to owns the row, as `owner%` below does), `references% source → records kinds% kind
[Kind.claim, Kind.premise]` one restricted to the parent rows whose column `kind` is one of those
listed, a list literal, a name or a term in parentheses (`kinds% kind claimKinds`), `references% target →
records allowed% edgeEnds (fact, End.target, kind)` one restricted to the parent rows whose `kind`
makes with the child row's `fact` and the endpoint `End.target` a row of the constant relation
`edgeEnds`, an `Allowance`, and `references% target → records where% fun edge record ↦ allowed
edge.fact record.fact` one restricted to the parent rows that a predicate of the child row and the
parent row accepts, for a rule that data cannot state.  `mandatory% record → records` requires every
row of `records` to be referred to by a row of the table through `record`, and `mandatory% record →
records for% fun record ↦ record.kind == Kind.claim` every row that the predicate accepts.  Both
take several columns too, `references% (record, position) → items` and `mandatory% (record,
position) → items`, for a parent whose primary key is those columns in that order: a row of a
table that marks or extends an item of a list belongs to that item, and an item may need one.  `index%
Snapshot.questionsByInquiry` maintains the index in that field, by the column in its type.
`root%` declares the table a root of ownership, whose rows operations append, each its own owner;
`owner% inquiry → inquiries` that every row belongs to the row of the table `inquiries`, a root or
itself owned, whose primary key is the row's `inquiry`; and `loaded%` that only the loader writes the table.  The
schema audit requires every table to declare one of the three.
`subtypes% records (fact) [verdicts ↦ Fact.verdict, labels ↦ Fact.label]` declares the tables
`verdicts` and `labels`, keyed by the primary key of the supertype table `records`, as its subtypes
for the records whose column `fact` has the value given, which share no key, and a trailing
`covering%` adds that every record with one of those values is of one of them, or `exhaustive%`
that every record is, whatever its value.  A member may be
for several values, `texts ↦ values% [Fact.claim, Fact.premise]`, or for those that a predicate
accepts, `untyped ↦ family% Fact.isUntyped`.  `tables% [questions,
answers]` is the list of those tables as `AnyTable`s; unlike a list literal with coercions, it
elaborates for any number of tables.  Names in diagnostics come from the same identifiers as the
projections. -/

declare_syntax_cat tableColumns
syntax "(" "*" ")" : tableColumns
syntax "(" ident,+ ")" : tableColumns

declare_syntax_cat tableClause
syntax "unique% " tableColumns : tableClause
syntax "references% " ident " → " ident : tableClause
syntax "parent% " ident " → " ident : tableClause
syntax "references% " ident " → " ident " kinds% " ident term:max : tableClause
syntax "references% " ident " → " ident " allowed% " ident " (" ident ", " term ", " ident ")" :
  tableClause
syntax "references% " ident " → " ident " where% " term : tableClause
syntax "mandatory% " ident " → " ident : tableClause
syntax "mandatory% " ident " → " ident " for% " term : tableClause
syntax "references% " "(" ident,+ ")" " → " ident : tableClause
syntax "references% " "(" ident,+ ")" " → " ident " where% " term : tableClause
syntax "mandatory% " "(" ident,+ ")" " → " ident : tableClause
syntax "mandatory% " "(" ident,+ ")" " → " ident " for% " term : tableClause
syntax "index% " ident : tableClause
syntax "root%" : tableClause
syntax "owner% " ident " → " ident : tableClause
syntax "loaded%" : tableClause

syntax "table% " ident tableColumns (ppLine tableClause)* : term
/-- A table whose field is written by `setter`, a function from the snapshot and the field's rows to
the snapshot (`table_rows%`'s grouped structures, whose fields are not the tables). -/
syntax "table% " ident tableColumns " set% " term (ppLine tableClause)* : term

declare_syntax_cat subtypeFacts
syntax "values% " "[" term,* "]" : subtypeFacts
syntax "family% " term : subtypeFacts
syntax term : subtypeFacts

syntax "subtypes% " ident " (" ident ")" " [" (ident " ↦ " subtypeFacts),* "]" : term
syntax "subtypes% " ident " (" ident ")" " [" (ident " ↦ " subtypeFacts),* "]" " covering%" :
  term
syntax "subtypes% " ident " (" ident ")" " [" (ident " ↦ " subtypeFacts),* "]" " exhaustive%" :
  term

syntax "tables% " " [" ident,* "]" : term

open Lean in
/-- The name and projection of a list of columns. -/
private meta def columnsKey : TSyntax `tableColumns → MacroM (String × Term)
  | `(tableColumns| (*)) => do
    let row := mkIdent `row
    return ("*", ← `(fun $row ↦ $row))
  | `(tableColumns| ($columns,*)) => do
    let columns := columns.getElems
    let row := mkIdent `row
    let fields : Array Term := columns.map fun column ↦ mkIdentFrom column (`row ++ column.getId)
    let tuple ← match fields.back? with
      | none => Macro.throwUnsupported
      | some last => fields.pop.foldrM (fun field rest ↦ `(($field, $rest))) last
    let name := ", ".intercalate (columns.map (·.getId.toString)).toList
    return (name, ← `(fun $row ↦ $tuple))
  | _ => Macro.throwUnsupported

open Lean in
/-- The function that reads the field `field` of a snapshot, own or inherited. -/
private meta def fieldGetter (field : Ident) : MacroM Term := do
  let .str owner name := field.getId | Macro.throwUnsupported
  let snapshot := mkIdent `snapshot
  `(fun ($snapshot : $(mkIdent owner)) ↦ $(mkIdent (`snapshot ++ .mkSimple name)))

open Lean in
/-- The function that replaces the field `field` of a snapshot. -/
private meta def fieldSetter (field : Ident) : MacroM (String × Term) := do
  let .str owner name := field.getId | Macro.throwUnsupported
  let snapshot := mkIdent `snapshot
  let value := mkIdent `value
  return (name, ← `(fun ($snapshot : $(mkIdent owner)) $value ↦
    { $snapshot with $(mkIdent (.mkSimple name)):ident := $value }))

open Lean in
/-- The values that a member of a subtyping is for: one value, a list of them, or a family that a
predicate accepts. -/
private meta def factSet : TSyntax `subtypeFacts → MacroM Term
  | `(subtypeFacts| values% [$values,*]) => `(FactSet.values [$values,*])
  | `(subtypeFacts| family% $accepts:term) => `(FactSet.family $accepts)
  | `(subtypeFacts| $value:term) => `(FactSet.values [$value])
  | _ => Macro.throwUnsupported

open Lean in
/-- The table `table` with the clause `clause` added, as `table%` writes it; the terms it makes take
the clause's position, and a column's projection the column's, so that an error in them is
reported there. -/
private meta def addClause (table : Term) (clause : TSyntax `tableClause) : MacroM Term := do
  let row := mkIdent `row
  let child := mkIdent `child
  let parent := mkIdent `parent
  match clause with
  | `(tableClause| unique% $columns:tableColumns) =>
    let (name, key) ← columnsKey columns
    `(Table.unique $table $(Syntax.mkStrLit name) $key)
  | `(tableClause| references% $column:ident → $target:ident) =>
    let projection := mkIdentFrom column (`row ++ column.getId)
    `(Table.references $table $(Syntax.mkStrLit column.getId.toString)
      (fun $row ↦ $projection) $target)
  | `(tableClause| parent% $column:ident → $target:ident) =>
    let projection := mkIdentFrom column (`row ++ column.getId)
    `(Table.owned (Table.references $table $(Syntax.mkStrLit column.getId.toString)
      (fun $row ↦ $projection) $target) $(Syntax.mkStrLit column.getId.toString)
      (fun $row ↦ $projection) $target)
  | `(tableClause| references% $column:ident → $target:ident kinds% $kind:ident $kinds) =>
    let projection := mkIdentFrom column (`row ++ column.getId)
    let parentKind := mkIdentFrom kind (`parent ++ kind.getId)
    `(Table.references $table $(Syntax.mkStrLit column.getId.toString)
      (fun $row ↦ $projection) $target
      (.facts $(Syntax.mkStrLit kind.getId.toString) (fun $parent ↦ $parentKind) $kinds))
  | `(tableClause| references% $column:ident → $target:ident allowed% $relation:ident
      ($childColumn:ident, $endpoint:term, $kind:ident)) =>
    let projection := mkIdentFrom column (`row ++ column.getId)
    let childValue := mkIdentFrom childColumn (`row ++ childColumn.getId)
    let parentKind := mkIdentFrom kind (`parent ++ kind.getId)
    `(Table.references $table $(Syntax.mkStrLit column.getId.toString)
      (fun $row ↦ $projection) $target
      (.allowance $(Syntax.mkStrLit childColumn.getId.toString) (fun $row ↦ $childValue)
        $relation $endpoint $(Syntax.mkStrLit kind.getId.toString) (fun $parent ↦ $parentKind)))
  | `(tableClause| references% $column:ident → $target:ident where% $allowed:term) =>
    let projection := mkIdentFrom column (`row ++ column.getId)
    `(Table.references $table $(Syntax.mkStrLit column.getId.toString)
      (fun $row ↦ $projection) $target (.predicate fun $child $parent ↦ $allowed $child $parent))
  | `(tableClause| mandatory% $column:ident → $target:ident) =>
    let projection := mkIdentFrom column (`row ++ column.getId)
    `(Table.mandatory $table $(Syntax.mkStrLit column.getId.toString)
      (fun $row ↦ $projection) $target)
  | `(tableClause| mandatory% $column:ident → $target:ident for% $scope:term) =>
    let projection := mkIdentFrom column (`row ++ column.getId)
    `(Table.mandatory $table $(Syntax.mkStrLit column.getId.toString)
      (fun $row ↦ $projection) $target (fun $parent ↦ $scope $parent))
  | `(tableClause| references% ($columns,*) → $target:ident) => do
    let (name, key) ← columnsKey (← `(tableColumns| ($columns,*)))
    `(Table.references $table $(Syntax.mkStrLit name) $key $target)
  | `(tableClause| references% ($columns,*) → $target:ident where% $allowed:term) => do
    let (name, key) ← columnsKey (← `(tableColumns| ($columns,*)))
    `(Table.references $table $(Syntax.mkStrLit name) $key $target
      (.predicate fun $child $parent ↦ $allowed $child $parent))
  | `(tableClause| mandatory% ($columns,*) → $target:ident) => do
    let (name, key) ← columnsKey (← `(tableColumns| ($columns,*)))
    `(Table.mandatory $table $(Syntax.mkStrLit name) $key $target)
  | `(tableClause| mandatory% ($columns,*) → $target:ident for% $scope:term) => do
    let (name, key) ← columnsKey (← `(tableColumns| ($columns,*)))
    `(Table.mandatory $table $(Syntax.mkStrLit name) $key $target (fun $parent ↦ $scope $parent))
  | `(tableClause| index% $index:ident) =>
    let (name, setter) ← fieldSetter index
    `(Table.index $table $(Syntax.mkStrLit name) $(← fieldGetter index) $setter)
  | `(tableClause| root%) => `(Table.root $table)
  | `(tableClause| owner% $column:ident → $target:ident) =>
    let projection := mkIdentFrom column (`row ++ column.getId)
    `(Table.owned $table $(Syntax.mkStrLit column.getId.toString)
      (fun $row ↦ $projection) $target)
  | `(tableClause| loaded%) => `(Table.loaded $table)
  | _ => Macro.throwUnsupported

open Lean in
macro_rules
  | `(table% $field:ident $primary:tableColumns $clauses:tableClause*) => do
    let (primaryName, primaryKey) ← columnsKey primary
    let (name, setter) ← fieldSetter field
    let mut table ← `(Table.make $(Syntax.mkStrLit name) $(← fieldGetter field) $setter
        $(Syntax.mkStrLit primaryName) $primaryKey)
    for clause in clauses do
      table ← withRef clause (addClause table clause)
    return table
  | `(table% $field:ident $primary:tableColumns set% $setter:term $clauses:tableClause*) => do
    let (primaryName, primaryKey) ← columnsKey primary
    let (name, _) ← fieldSetter field
    let mut table ← `(Table.make $(Syntax.mkStrLit name) $(← fieldGetter field) $setter
        $(Syntax.mkStrLit primaryName) $primaryKey)
    for clause in clauses do
      table ← withRef clause (addClause table clause)
    return table
  | `(subtypes% $supertype:ident ($column:ident) [$[$members:ident ↦ $facts:subtypeFacts],*]) => do
    let members ← (members.zip facts).mapM fun (member, facts) ↦ do
      `(SubtypeMember.of $member $(← factSet facts))
    let row := mkIdent `row
    `(Subtyping.make $supertype (fun $row ↦ $(mkIdent (`row ++ column.getId))) [$members,*])
  | `(subtypes% $supertype:ident ($column:ident) [$[$members:ident ↦ $facts:subtypeFacts],*]
      covering%) => do
    let members ← (members.zip facts).mapM fun (member, facts) ↦ do
      `(SubtypeMember.of $member $(← factSet facts))
    let row := mkIdent `row
    `(Subtyping.make $supertype (fun $row ↦ $(mkIdent (`row ++ column.getId))) [$members,*]
      .covering)
  | `(subtypes% $supertype:ident ($column:ident) [$[$members:ident ↦ $facts:subtypeFacts],*]
      exhaustive%) => do
    let members ← (members.zip facts).mapM fun (member, facts) ↦ do
      `(SubtypeMember.of $member $(← factSet facts))
    let row := mkIdent `row
    `(Subtyping.make $supertype (fun $row ↦ $(mkIdent (`row ++ column.getId))) [$members,*]
      .exhaustive)
  | `(tables% [$tables,*]) => do
    let tables ← tables.getElems.mapM fun table ↦ `(AnyTable.mk $table)
    `([$tables,*])

end Relational
