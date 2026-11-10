module

public import Lean
public import Relational.Lens
public import Relational.SchemaAudit
public meta import Relational.SchemaAudit

-- all of it runs while `schema_laws%` elaborates
public meta section

/-! `schema_laws% Snapshot schema`, for a schema that passed `#audit_schema`, proves the laws of its
readers and writers (`Schema.Wiring`, in Relational/Lens.lean) and declares them as the instance
`schema.laws.wiring`.  It is a command of its own, for a module of its own, so that the modules that
only read the tables do not elaborate the proofs.

The snapshot is read as the audit reads it: its fields, own and inherited, each a group of tables
that `table_rows%` declared or a field holding `Rows` or an `Index`.  The command declares, in the
namespace `schema.laws`:

- `Field`, an enumeration of the snapshot's fields, and for each group field an enumeration of the
  tables in the group, named by the field;
- `FieldT`, `Idx` and `Slot`, the type of each field, the parts of each field (the group's tables,
  or `Unit` for a field that is one part) and the type of each part;
- `outer`, the family of the snapshot's fields, and `inner`, for each field the family of its parts
  (`Family.single` for a field that is one part), with their laws (`outer_lawful`, `inner<k>_lawful`,
  `inner_lawful`), and `F`, their composition, with `F_lawful`;
- `rank`, which numbers each part by its position: `(p, 0)` for the table at position `p` of the
  schema's tables, `(p, j + 1)` for its `j`th index;
- for each table `t`, the bridges `t.rows_F` and `t.set_F`, which state `t.rows` and `t.set` as the
  family's part; and `wired<k>`, that the tables from position `k` on and their indexes are parts of
  `F` (`Wired`), each from the next, so that no proof walks the list of tables from its start;
- `wired`, for the schema's tables, and the instance `wiring`.

Every proof is built here as a term and handed to the kernel (`addDecl`), with no tactic and no
elaboration: the laws of each family by case analysis on both parts, each case `rfl` or absurd; the
bridges and the wiring by `rfl`.  So the cost of a schema is the kernel's.  The families' laws
enumerate pairs of a family's parts: the square of the number of fields, and of the group size
(`groupSize`) for each group, not of the number of tables. -/

namespace Relational

open Lean Elab Command Meta SchemaMeta

namespace SchemaLaws

/-- A part of a field: a table of a group, as the group's structure holds it. -/
structure Part where
  /-- The table's field in the group's structure. -/
  field : Name
  /-- Its constructor of the group's enumeration. -/
  ctor : Expr
  /-- The type of the field, `Rows key`. -/
  type : Expr
  /-- Reads it from the group: `fun group ↦ group.field`. -/
  get : Expr
  /-- Replaces it in the group: `fun group value ↦ { group with field := value }`. -/
  set : Expr

/-- A field of the snapshot, own or inherited. -/
structure LawField where
  field : Name
  /-- Its constructor of `Field`. -/
  ctor : Expr
  /-- The type of the field: a group's structure, `Rows key` or an `Index`. -/
  type : Expr
  /-- Reads it from a snapshot. -/
  get : Expr
  /-- Replaces it in a snapshot. -/
  set : Expr
  /-- For a group field, its enumeration and its tables. -/
  group? : Option (Name × Array Part)

/-- `enum.casesOn (motive := motive) major branches`, at the universe of the motive. -/
def casesOn (enum : Name) (motive major : Expr) (branches : Array Expr) : MetaM Expr := do
  let level ← forallTelescope (← inferType motive) fun _ body ↦ do
    match ← whnf body with
    | .sort level => pure level
    | other => throwError "the motive {motive} does not give a sort but {other}"
  return mkAppN (mkConst (enum ++ `casesOn) [level]) (#[motive, major] ++ branches)

/-- `fun (x : type) ↦ body x`. -/
def lambda (name : Name) (type : Expr) (body : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD name type fun x ↦ do mkLambdaFVars #[x] (← body x)

/-- `(x : type) → body x`. -/
def pi (name : Name) (type : Expr) (body : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD name type fun x ↦ do mkForallFVars #[x] (← body x)

/-- Adds a definition, its body exposed to importing modules. -/
def define (name : Name) (type value : Expr) (reducible : Bool := false) : MetaM Unit := do
  addDecl (forceExpose := true) <| .defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
  if reducible then setReducibleAttribute name

/-- Adds a theorem. -/
def prove (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- The pair of numbers `(first, second)`. -/
def pair (first second : Nat) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkNatLit first)
    (mkNatLit second)

/-- The laws of the family `family : Family S ι Slot`, for `ι` the enumeration `enum` with the
constructors `ctors`, by cases on both parts: `rfl` for every case but the same part twice in
`get_set_ne`, which is absurd. -/
def lawfulProof (S enum : Expr) (enumName : Name) (ctors : Array Expr) (slot family : Expr) :
    MetaM Expr := do
  let get (s i : Expr) := mkAppN (mkConst ``Family.get) #[S, enum, slot, family, s, i]
  let set (s i v : Expr) := mkAppN (mkConst ``Family.set) #[S, enum, slot, family, s, i, v]
  let slotOf (i : Expr) := (mkApp slot i).headBeta
  let getSet ← lambda `s S fun s ↦ lambda `i enum fun i ↦ do
    let motive ← lambda `i enum fun i ↦ pi `v (slotOf i) fun v ↦
      mkEq (get (set s i v) i) v
    casesOn enumName motive i (← ctors.mapM fun c ↦
      lambda `v (slotOf c) fun v ↦ pure (mkApp2 (mkConst ``Eq.refl [1]) (slotOf c) v))
  let getSetNe ← lambda `s S fun s ↦ lambda `i enum fun i ↦ do
    let motive ← lambda `i enum fun i ↦ pi `j enum fun j ↦ pi `v (slotOf i) fun v ↦ do
      mkArrow (mkNot (← mkEq i j)) (← mkEq (get (set s i v) j) (get s j))
    casesOn enumName motive i (← ctors.mapIdxM fun a c ↦ lambda `j enum fun j ↦ do
      let inner ← lambda `j enum fun j ↦ pi `v (slotOf c) fun v ↦ do
        mkArrow (mkNot (← mkEq c j)) (← mkEq (get (set s c v) j) (get s j))
      casesOn enumName inner j (← ctors.mapIdxM fun b d ↦ do
        lambda `v (slotOf c) fun v ↦ do lambda `h (mkNot (← mkEq c d)) fun h ↦ do
          if a == b then
            let goal ← mkEq (get (set s c v) d) (get s d)
            pure (mkApp2 (mkConst ``False.elim [0]) goal
              (mkApp h (mkApp2 (mkConst ``Eq.refl [1]) enum c)))
          else pure (mkApp2 (mkConst ``Eq.refl [1]) (slotOf d) (get s d))))
  return mkAppN (mkConst ``Family.Lawful.mk) #[S, enum, slot, family, getSet, getSetNe]

/-- The constructors of the enumeration `enum`, as constants. -/
def ctorsOf (enum : Name) : MetaM (Array Expr) := do
  let .inductInfo info ← getConstInfo enum | throwError "{enum} is not an inductive type"
  return info.ctors.toArray.map (mkConst ·)

/-- The value of the definition `name`. -/
def valueOf (name : Name) : MetaM Expr := do
  let .defnInfo info ← getConstInfo name | throwError "{name} is not a definition"
  return info.value

end SchemaLaws

open SchemaLaws

syntax (name := schemaLawsCommand) "schema_laws% " ident ident : command

@[command_elab schemaLawsCommand] def elabSchemaLaws : CommandElab := fun stx ↦ do
  let snapshot : Ident := ⟨stx[1]⟩
  let schema : Ident := ⟨stx[2]⟩
  let (snapshotName, schemaName) ← liftTermElabM do
    return (← realizeGlobalConstNoOverloadWithInfo snapshot,
      ← realizeGlobalConstNoOverloadWithInfo schema)
  let space := schemaName.getPrefix
  let laws := schemaName ++ `laws
  let positions := schemaName ++ `positions
  unless (← getEnv).contains (positions ++ `tables_eq) do
    throwErrorAt schema "{schemaName} has not passed #audit_schema"
  -- the fields, and for each group field the tables in it
  let fields : Array (Name × Option (Name × Array Name)) ← liftTermElabM do
    let env ← getEnv
    getStructureFieldsFlattened env snapshotName (includeSubobjectFields := false) |>.mapM
      fun field ↦ do
        match ← groupOf? snapshotName field with
        | some group =>
          return (field, some (group, getStructureFieldsFlattened env group
            (includeSubobjectFields := false)))
        | none => return (field, none)
  -- the enumerations, declared as inductive types, each constructor named by its field
  let fieldEnum := laws ++ `Field
  let enumOf (field : Name) : Name := laws ++ field
  let enumCommand (name : Name) (ctors : Array Name) : CommandElabM Unit := do
    let ctors ← ctors.mapM fun ctor ↦ `(Parser.Command.ctor| | $(mkIdent ctor):ident)
    elabCommand (← `(command| inductive $(mkIdent (`_root_ ++ name)):ident where $[$ctors]*))
  enumCommand fieldEnum (fields.map (·.1))
  for (field, group?) in fields do
    if let some (_, tables) := group? then enumCommand (enumOf field) tables
  liftTermElabM do
    let S := mkConst snapshotName
    let Field := mkConst fieldEnum
    let mut infos : Array LawField := #[]
    for (field, group?) in fields do
      let get ← projectionOf snapshotName field
      let set ← setterOf snapshotName field
      let type ← withLocalDeclD `s S fun s ↦ inferType (mkApp get s).headBeta
      let group? ← group?.mapM fun (structure_, tables) ↦ do
        let parts ← tables.mapM fun table ↦ do
          let get ← projectionOf structure_ table
          let set ← setterOf structure_ table
          let type ← withLocalDeclD `g (mkConst structure_) fun g ↦ inferType (mkApp get g).headBeta
          return { field := table, ctor := mkConst (enumOf field ++ table), type, get, set : Part }
        return (enumOf field, parts)
      infos := infos.push { field, ctor := mkConst (fieldEnum ++ field), type, get, set, group? }
    -- the schema's tables in field order, as the audit found them: the tables of the groups and the
    -- fields holding Rows; and where each index is, by its table's position and its own
    let mut tables : Array Name := #[]
    let mut indexOwners : Array (Name × Nat × Nat) := #[]
    for info in infos do
      match info.group? with
      | some (_, parts) => for part in parts do tables := tables.push part.field
      | none =>
        if (← whnf info.type).getAppFn.constName? == some ``Rows then
          tables := tables.push info.field
    for (field, p) in tables.zipIdx do
      let indexes ← elementsOf (← mkAppM ``Table.indexes #[mkConst (space ++ field)])
      for (index, j) in indexes.zipIdx do
        let name ← stringOf (← mkAppM ``TableIndex.name #[index])
        indexOwners := indexOwners.push (Name.mkSimple name, p, j)
    let positionOf (field : Name) : MetaM Nat := do
      let some p := tables.idxOf? field | throwError "{field} is not a table of {schemaName}"
      return p
    let rankOf (field : Name) : MetaM Expr := do
      if let some (_, p, j) := indexOwners.find? (·.1 == field) then return pair p (j + 1)
      return pair (← positionOf field) 0
    -- the types of the fields, their parts and the parts' types
    let typeMotive ← lambda `a Field fun _ ↦ pure (mkSort Level.one)
    let FieldT ← lambda `a Field fun a ↦ casesOn fieldEnum typeMotive a (infos.map (·.type))
    define (laws ++ `FieldT) (← mkArrow Field (mkSort Level.one)) FieldT (reducible := true)
    let FieldT := mkConst (laws ++ `FieldT)
    let Idx ← lambda `a Field fun a ↦ casesOn fieldEnum typeMotive a (infos.map fun info ↦
      match info.group? with
      | some (enum, _) => mkConst enum
      | none => mkConst ``Unit)
    define (laws ++ `Idx) (← mkArrow Field (mkSort Level.one)) Idx (reducible := true)
    let Idx := mkConst (laws ++ `Idx)
    let Id := mkApp2 (mkConst ``Sigma [0, 0]) Field Idx
    let fst (i : Expr) := mkApp3 (mkConst ``Sigma.fst [0, 0]) Field Idx i
    let snd (i : Expr) := mkApp3 (mkConst ``Sigma.snd [0, 0]) Field Idx i
    let mkId (a k : Expr) := mkApp4 (mkConst ``Sigma.mk [0, 0]) Field Idx a k
    -- by cases on the field, a function of its parts
    let byField (motiveBody : Expr → Expr) (branches : Array Expr) (i : Expr) : MetaM Expr := do
      let motive ← lambda `a Field fun a ↦ mkArrow (mkApp Idx a) (motiveBody a)
      return mkApp (← casesOn fieldEnum motive (fst i) branches) (snd i)
    let partBranches (result : Expr) (leaf : LawField → MetaM Expr) (ofPart : Part → MetaM Expr) :
        MetaM (Array Expr) := infos.mapM fun info ↦ do
      match info.group? with
      | some (enum, parts) =>
        let enumType := mkConst enum
        lambda `k enumType fun k ↦ do
          casesOn enum (← lambda `k enumType fun _ ↦ pure result) k (← parts.mapM ofPart)
      | none => lambda `k (mkConst ``Unit) fun _ ↦ leaf info
    let Slot ← lambda `i Id fun i ↦ do
      byField (fun _ ↦ mkSort Level.one) (← partBranches (mkSort Level.one) (pure ·.type)
        (pure ·.type)) i
    define (laws ++ `Slot) (← mkArrow Id (mkSort Level.one)) Slot (reducible := true)
    let Slot := mkConst (laws ++ `Slot)
    let rankType := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
    let rank ← lambda `i Id fun i ↦ do
      byField (fun _ ↦ rankType) (← partBranches rankType (rankOf ·.field) (rankOf ·.field)) i
    define (laws ++ `rank) (← mkArrow Id rankType) rank
    let rank := mkConst (laws ++ `rank)
    -- the family of the fields
    let familyType (S ι slot : Expr) := mkApp3 (mkConst ``Family) S ι slot
    let outerType := familyType S Field FieldT
    let outerGet ← lambda `s S fun s ↦ lambda `a Field fun a ↦ do
      casesOn fieldEnum (← lambda `a Field fun a ↦ pure (mkApp FieldT a)) a
        (infos.map fun info ↦ (mkApp info.get s).headBeta)
    let outerSet ← lambda `s S fun s ↦ lambda `a Field fun a ↦ do
      casesOn fieldEnum (← lambda `a Field fun a ↦ mkArrow (mkApp FieldT a) S) a
        (infos.map fun info ↦ (mkApp info.set s).headBeta)
    define (laws ++ `outer) outerType
      (mkAppN (mkConst ``Family.mk) #[S, Field, FieldT, outerGet, outerSet])
    let outer := mkConst (laws ++ `outer)
    prove (laws ++ `outer_lawful) (mkAppN (mkConst ``Family.Lawful) #[S, Field, FieldT, outer])
      (← lawfulProof S Field fieldEnum (infos.map (·.ctor)) FieldT outer)
    -- the family of each field's parts
    let partSlot (a : Expr) : MetaM Expr := lambda `k (mkApp Idx a) fun k ↦ pure (mkApp Slot (mkId a k))
    let innerType (a : Expr) : MetaM Expr := do
      return familyType (mkApp FieldT a) (mkApp Idx a) (← partSlot a)
    let lawfulType (S ι slot family : Expr) := mkAppN (mkConst ``Family.Lawful) #[S, ι, slot, family]
    let mut inners : Array Expr := #[]
    let mut innerLaws : Array Expr := #[]
    for (info, a) in infos.zipIdx do
      let name := laws ++ .mkSimple s!"inner{a}"
      let lawName := laws ++ .mkSimple s!"inner{a}_lawful"
      let slot ← partSlot info.ctor
      match info.group? with
      | some (enumName, parts) =>
        let enum := mkConst enumName
        let get ← lambda `x info.type fun x ↦ lambda `k enum fun k ↦ do
          casesOn enumName (← lambda `k enum fun k ↦ pure (mkApp slot k).headBeta) k
            (parts.map fun part ↦ (mkApp part.get x).headBeta)
        let set ← lambda `x info.type fun x ↦ lambda `k enum fun k ↦ do
          casesOn enumName (← lambda `k enum fun k ↦ mkArrow (mkApp slot k).headBeta info.type) k
            (parts.map fun part ↦ (mkApp part.set x).headBeta)
        define name (← innerType info.ctor)
          (mkAppN (mkConst ``Family.mk) #[info.type, enum, slot, get, set])
        prove lawName (lawfulType info.type enum slot (mkConst name))
          (← lawfulProof info.type enum enumName (parts.map (·.ctor)) slot (mkConst name))
      | none =>
        define name (← innerType info.ctor) (mkApp (mkConst ``Family.single) info.type)
        prove lawName (lawfulType info.type (mkConst ``Unit) slot (mkConst name))
          (mkApp (mkConst ``Family.single_lawful) info.type)
      inners := inners.push (mkConst name)
      innerLaws := innerLaws.push (mkConst lawName)
    let innerAllType ← pi `a Field innerType
    let inner ← lambda `a Field fun a ↦ do
      casesOn fieldEnum (← lambda `a Field innerType) a inners
    define (laws ++ `inner) innerAllType inner
    let inner := mkConst (laws ++ `inner)
    let innerLawType (a : Expr) : MetaM Expr := do
      return lawfulType (mkApp FieldT a) (mkApp Idx a) (← partSlot a) (mkApp inner a)
    prove (laws ++ `inner_lawful) (← pi `a Field innerLawType) (← lambda `a Field fun a ↦ do
      casesOn fieldEnum (← lambda `a Field innerLawType) a innerLaws)
    -- their composition
    let F := mkAppN (mkConst ``Family.compose) #[S, Field, FieldT, Idx, Slot, outer, inner]
    define (laws ++ `F) (familyType S Id Slot) F
    let F := mkConst (laws ++ `F)
    prove (laws ++ `F_lawful) (lawfulType S Id Slot F)
      (mkAppN (mkConst ``Family.compose_lawful) #[S, Field, FieldT, Idx, Slot, outer, inner,
        mkConst (laws ++ `outer_lawful), mkConst (laws ++ `inner_lawful)])
    -- the bridges of each table, and the part of each table and index
    let partOf (field : Name) : Option Expr := infos.findSome? fun info ↦
      match info.group? with
      | some (_, parts) => parts.findSome? fun part ↦
        if part.field == field then some (mkId info.ctor part.ctor) else none
      | none => if info.field == field then some (mkId info.ctor (mkConst ``Unit.unit)) else none
    let getF (s i : Expr) := mkAppN (mkConst ``Family.get) #[S, Id, Slot, F, s, i]
    let setF (s i v : Expr) := mkAppN (mkConst ``Family.set) #[S, Id, Slot, F, s, i, v]
    for field in tables do
      let table := mkConst (space ++ field)
      let some i := partOf field | throwError "no part for the table {field}"
      let rowsType ← withLocalDeclD `s S fun s ↦ do
        inferType (← mkAppM ``Table.rows #[table, s])
      prove (space ++ field ++ `rows_F) (← pi `s S fun s ↦ do
          mkEq (← mkAppM ``Table.rows #[table, s]) (getF s i))
        (← lambda `s S fun s ↦ do
          pure (mkApp2 (mkConst ``Eq.refl [1]) rowsType (← mkAppM ``Table.rows #[table, s])))
      prove (space ++ field ++ `set_F) (← pi `s S fun s ↦ pi `v rowsType fun v ↦ do
          mkEq (← mkAppM ``Table.set #[table, s, v]) (setF s i v))
        (← lambda `s S fun s ↦ lambda `v rowsType fun v ↦ do
          pure (mkApp2 (mkConst ``Eq.refl [1]) S (← mkAppM ``Table.set #[table, s, v])))
    -- the tables from each position on are wired, each from the next
    let fromName (k : Nat) : Name := positions ++ .mkSimple s!"from{k}"
    let wiredName (k : Nat) : Name := laws ++ .mkSimple s!"wired{k}"
    let wiredType (k : Nat) (entries : Expr) : Expr :=
      mkAppN (mkConst ``Wired) #[S, Id, Slot, F, rank, mkNatLit k, entries]
    let count := tables.size
    prove (wiredName count) (wiredType count (mkConst (fromName count)))
      (mkAppN (mkConst ``Wired.nil) #[S, Id, Slot, F, rank, mkNatLit count])
    for (field, k) in tables.zipIdx.reverse do
      let value ← valueOf (fromName k)
      let #[_, entry, rest] := value.getAppArgs
        | throwError "{fromName k} is not a table followed by the rest"
      let table := mkConst (space ++ field)
      let some i := partOf field | throwError "no part for the table {field}"
      let slotType := mkApp Slot i
      let reflType (type : Expr) := mkApp2 (mkConst ``Eq.refl [2]) (mkSort Level.one) type
      let rowsEq ← lambda `s S fun s ↦ pure (mkApp (mkConst (space ++ field ++ `rows_F)) s)
      let rowsType ← withLocalDeclD `s S fun s ↦ do
        inferType (← mkAppM ``Table.rows #[table, s])
      let setEq ← lambda `s S fun s ↦ lambda `r rowsType fun r ↦
        pure (mkApp2 (mkConst (space ++ field ++ `set_F)) s r)
      -- the table's indexes, each a part of its own
      let tableType ← whnf (← inferType table)
      let #[_, Row, Key, order, key] := tableType.getAppArgs
        | throwError "{field} is not a table: {tableType}"
      let indexes ← elementsOf (← mkAppM ``Table.indexes #[table])
      let indexType := mkAppN (mkConst ``TableIndex) #[S, Row, Key, order, key]
      let mut indexesWired := mkAppN (mkConst ``IndexesWired.nil)
        #[S, Id, Slot, F, rank, mkNatLit k, Row, Key, order, key, mkNatLit indexes.size]
      -- `TableIndex` lives in `Type 1`: it holds the type of its column
      let some listLevel := (← getLevel indexType).dec
        | throwError "schema_laws%: the indexes of the table {field} have the type {indexType}, which is not in a universe above Type 0"
      let mut tail := mkApp (mkConst ``List.nil [listLevel]) indexType
      for (index, j) in indexes.zipIdx.reverse do
        let name ← stringOf (← mkAppM ``TableIndex.name #[index])
        let some part := partOf (.mkSimple name) | throwError "no part for the index {name}"
        let indexSlot := mkApp Slot part
        let getEq ← lambda `s S fun s ↦ pure (mkApp2 (mkConst ``Eq.refl [1]) indexSlot (getF s part))
        let valueType ← whnf (← inferType (← mkAppM ``TableIndex.get #[index])) >>= fun t ↦
          match t with
          | .forallE _ _ body _ => pure body
          | other => throwError "the index {name} does not read a snapshot: {other}"
        let setEq ← lambda `s S fun s ↦ lambda `v valueType fun v ↦
          pure (mkApp2 (mkConst ``Eq.refl [1]) S (setF s part v))
        indexesWired := mkAppN (mkConst ``IndexesWired.cons)
          #[S, Id, Slot, F, rank, mkNatLit k, Row, Key, order, key, mkNatLit j, index, part, tail,
            reflType indexSlot, mkApp2 (mkConst ``Eq.refl [1]) rankType (mkApp rank part),
            getEq, setEq, indexesWired]
        tail := mkApp3 (mkConst ``List.cons [listLevel]) indexType index tail
      prove (wiredName k) (wiredType k (mkConst (fromName k)))
        (mkAppN (mkConst ``Wired.cons)
          #[S, Id, Slot, F, rank, mkNatLit k, entry, i, rest, reflType slotType,
            mkApp2 (mkConst ``Eq.refl [1]) rankType (mkApp rank i), rowsEq, setEq, indexesWired,
            mkConst (wiredName (k + 1))])
    -- the schema's tables, and the laws
    let schemaC := mkConst schemaName
    let tablesEq := mkConst (positions ++ `tables_eq)
    let tablesOf ← mkAppM ``Schema.tables #[schemaC]
    let wired ← mkEqMPR (← mkCongrArg (← lambda `l (← inferType tablesOf) fun l ↦
      pure (wiredType 0 l)) tablesEq) (mkConst (wiredName 0))
    prove (laws ++ `wired) (wiredType 0 tablesOf) wired
    let wiringType ← mkAppM ``Schema.Wiring #[schemaC]
    prove (laws ++ `wiring) wiringType
      (← mkAppM ``Wired.wiring #[mkConst (laws ++ `F_lawful), mkConst (laws ++ `wired)])
    addInstance (laws ++ `wiring) .global (eval_prio default)

end Relational
