module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64PrimeTerminal
public meta import Lean

open Lean

private structure TypeDag where
  ids : Std.HashMap ExprStructEq Nat := {}
  nodes : Array String := #[]

private partial def typeDagVisit (e : Expr) : StateM TypeDag Nat := do
  let before : TypeDag ← get
  if let some i := before.ids[(⟨e⟩ : ExprStructEq)]? then return i
  let record ← match e with
    | .bvar i => pure (s!"bvar {i}")
    | .fvar i => pure ("fvar " ++ reprStr i)
    | .mvar i => pure ("mvar " ++ reprStr i)
    | .sort u => pure ("sort " ++ reprStr u)
    | .const n us => pure ("const " ++ reprStr n ++ " " ++ reprStr us)
    | .app f a => do
      let f ← typeDagVisit f
      let a ← typeDagVisit a
      pure (s!"app {f} {a}")
    | .lam n t b bi => do
      let t ← typeDagVisit t
      let b ← typeDagVisit b
      pure ("lam " ++ reprStr n ++ s!" {t} {b} " ++ reprStr bi)
    | .forallE n t b bi => do
      let t ← typeDagVisit t
      let b ← typeDagVisit b
      pure ("forallE " ++ reprStr n ++ s!" {t} {b} " ++ reprStr bi)
    | .letE n t v b nd => do
      let t ← typeDagVisit t
      let v ← typeDagVisit v
      let b ← typeDagVisit b
      pure ("letE " ++ reprStr n ++ s!" {t} {v} {b} " ++ reprStr nd)
    | .lit l => pure ("lit " ++ reprStr l)
    | .mdata d b => do
      let b ← typeDagVisit b
      pure (s!"mdata {d} {b}")
    | .proj n i b => do
      let b ← typeDagVisit b
      pure (s!"proj {n} {i} {b}")
  let s : TypeDag ← get
  let i := s.nodes.size
  set ({ ids := s.ids.insert ⟨e⟩ i, nodes := s.nodes.push record } : TypeDag)
  return i

run_cmd do
  let env ← getEnv
  let owner : Name :=
    `CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64PrimeTerminal
  let names := env.header.moduleNames
  let constants := env.constants.toList
  liftM <| IO.println s!"CENSUS_CONSTANTS {constants.length}"
  let mut count : Nat := 0
  for (name, ci) in constants do
    if isPrivateName name then continue
    let some idx := env.getModuleIdxFor? name | continue
    unless names[idx.toNat]! == owner do continue
    count := count + 1
    let axs ← collectAxioms name
    let bad := axs.filter fun n => !(#[``propext, ``Classical.choice, ``Quot.sound].contains n)
    unless bad.isEmpty do throwError "Unexpected axioms for {name}: {bad}"
    logInfo m!"TYPE_PRETTY {name}: {ci.type}"
    liftM <| IO.println s!"PUBLIC {names[idx.toNat]!} {name} AXIOMS {reprStr axs}"
    let (rootId, dag) := (typeDagVisit ci.type).run {}
    liftM <| IO.println s!"RAW_TYPE_BEGIN {name} OWNER {names[idx.toNat]!} FORMAT ExprStructEq_DAG"
    for i in [:dag.nodes.size] do
      liftM <| IO.println s!"NODE {i} {dag.nodes[i]!}"
    liftM <| IO.println s!"ROOT {rootId} NODE_COUNT {dag.nodes.size} LEVEL_PARAMS {reprStr ci.levelParams}"
    liftM <| IO.println s!"RAW_TYPE_END {name}"
  unless count > 0 do throwError "Missing public declarations: {count}"
  liftM <| IO.println s!"PUBLIC_COUNT {count}"
