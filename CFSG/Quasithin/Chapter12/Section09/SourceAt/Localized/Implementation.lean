module
import all CFSG.Quasithin.Chapter12.Section09.Intersections
import all CFSG.Quasithin.Chapter12.Section09.SourceInputs
import all CFSG.Quasithin.Chapter12.Section09.SourceSetup
import all CFSG.Quasithin.Chapter12.Section09.Terminal
import all CFSG.Quasithin.Chapter12.Section09.Hyperplanes
import all CFSG.Quasithin.Chapter12.Section08.Setup.ChosenLinearThree
import all CFSG.Quasithin.Chapter12.Section08.Setup.Completion
import all CFSG.Quasithin.Chapter12.Section08.Setup.Consumers
import all CFSG.Quasithin.Chapter12.Section08.Setup.Escape
import all CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction
import all CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Parabolic
import all CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Transport
import all CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry
import all CFSG.Quasithin.Chapter12.Section08.Setup.NaturalActions
import all CFSG.Quasithin.Chapter12.Section08.Setup.Normalizers
import all CFSG.Quasithin.Chapter12.Section08.Setup.PointCoreMovement
import all CFSG.Quasithin.Chapter12.Section08.Setup.RankTwoBase
import all CFSG.Quasithin.Chapter12.Section08.Setup.RankTwoConstruction
import all CFSG.Quasithin.Chapter12.Section08.Setup.SourceData
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Abelian
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Binary
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourCatalogue
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourEven
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourFinite
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourNormal
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourQuotients
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourRankOne
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourTernary
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourThree
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Janko
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.JankoComplete
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.JankoMathieu
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Mathieu
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.MathieuComplete
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Membership
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Models
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianAction
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianAmbient
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianBinaryAmalgam
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianBinaryFixed
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianCases
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianCenterAction
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianCenterQuotient
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianCompletion
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianComponents
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituentAction
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituentModels
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituentQuotient
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituents
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianExchanged
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianFixed
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianFixedLine
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianFourGeometry
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianGeometry
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianHypotheses
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianLift
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianLowRank
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianMathieu
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianMultiplicity
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianNatural
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianNormalizer
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianOrthogonal
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianOrthogonalGeometry
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianParabolics
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianPointWhole
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianRadicals
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianRecognition
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianRemaining
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianResidual
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianSeed
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianSeven
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianWhole
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalCaseFiveExclusion
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalCaseFiveGeometry
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalConstituentAction
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalConstituentNatural
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalConstituentRows
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalConstituentSource
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalDeletedDescent
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalDeletedFourActor
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalDeletedSection
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalPointDeletedModel
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Overgroups
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Plane
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.PointAction
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Quotients
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Sporadic
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.ThreeComplete
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.ThreeRadical
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.FusionConsequences
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.FusionGeometry
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.Complete
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.CoreMovement
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FivePlane
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourMixedPlane
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourPlaneLattice
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourPlaneOrbit
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourSeven
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MatchingBinary
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MixedBinary
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MixedKernel
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.Movement
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.Normalizers
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneClosure
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneReduction
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneResidual
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointBound
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointCentralizer
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointControl
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointJoin
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointModels
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointMultiplicity
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointOrder
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.QuadraticBound
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.SevenCore
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.Stages
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.Binary
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.Core
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.Cubic
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.InnerAction
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.Quotient
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalGeometry
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.WeakClosure.ComponentAction
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.WeakClosure.CoreGeometry
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.WeakClosure.OrbitControl
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource.WeakClosure
import all CFSG.Quasithin.Chapter12.Section09.NaturalSource

import all CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple

public import CFSG.Quasithin.Chapter12.Section09.SourceInputs
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
meta import Lean.Elab.Tactic
/-!
# The Section 12.9 source specialized to the original G,T

The existing proofs transmit universal earlier structural, recognition and
module inputs. Every actual use is at the original ambient group and Sylow.
This internal module reuses their compiled proofs with those precise local
inputs, retaining the proved universal known-simple uniqueness theorem.
The internal degree-four reduction is removed only by substituting the proved
original-row CaseFive exclusion, with its exact transformed type checked.

The intentional `import all` edges expose the existing private proof terms
within this package; no old source is changed. Every narrowed field application
checks the actual ambient type, instances, class and Sylow. Fully applied source
wrappers with aliased types are expanded to their original proofs. The shared
private theorem closure is checked against independently transformed types and
submitted to both the kernel expression checker and ordinary `addDecl`.
No universal source record is constructed and no axiom is introduced.

Only the two ordinary theorems below are the mathematical interface. Their
statements retain the actual higher-rank natural marking. In particular this
does not prove the separate initial degree-four natural-module reduction.

Source: Aschbacher--Smith 12.9.1--9, printed pp.857--864, refs/quasithin.pdf.
-/

open Lean Meta Elab Tactic Command
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.SourceAt.Localized
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.Chapter12.Section08
universe u
private structure EarlierAt {G : Type u} [Group G] [Finite G]
    (K : CFSG.Quasithin.GroupClass.{u}) (T : Sylow 2 G) : Prop where
  structural : Structural1222At K T
  uniqueness : Uniqueness127 K
  alternatives : Theorem12213At K T

private theorem knownUniqueness : Uniqueness127.{u} CFSG.KnownSimple.IsKnownSimple := by
  intro G _ _ hG T L hL
  exact CFSG.Quasithin.Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hL

private meta def oldNames : Array Name := #[
  ``EarlierSetupResults, ``Structural1222, ``Theorem12213,
  ``Theorem1222ModulesOfMany, ``CFSG.Quasithin.Chapter12.Section09.NaturalReduction]
private meta def kind (e : Expr) : Option Nat :=
  oldNames.findIdx? (e.getAppFn.isConstOf ·)
private meta def localKind (e : Expr) : Option Nat :=
  #[``EarlierAt, ``Structural1222At, ``Theorem12213At, ``Theorem1222ModulesAt].findIdx?
    (e.getAppFn.isConstOf ·)
private meta def fields : Array Name := #[
  ``EarlierSetupResults.structural, ``EarlierSetupResults.uniqueness,
  ``EarlierSetupResults.alternatives]
private meta def localFields : Array Name := #[
  ``EarlierAt.structural, ``EarlierAt.uniqueness, ``EarlierAt.alternatives]
private meta def scopeOK (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  s.startsWith "CFSG.Quasithin.Chapter12.Section08." ||
  s.startsWith "CFSG.Quasithin.Chapter12.Section09." ||
  s.startsWith "CFSG.Quasithin.Chapter12.Section02."
private meta def sylowVar : MetaM Expr := do
  let mut found : Option Expr := none
  for d in (← getLCtx) do
    if !d.isImplementationDetail && d.type.getAppFn.isConstOf ``Sylow then
      if found.isSome then throwError "Multiple Sylow binders in original declaration"
      found := some d.toExpr
  match found with
  | some t => return t
  | none => throwError "No original Sylow binder available for narrowing"
private meta def narrowType (t : Expr) (k : Nat) : MetaM Expr := do
  let T ← sylowVar
  let cls := t.getAppArgs[0]!
  match k with
  | 0 => mkAppM ``EarlierAt #[cls,T]
  | 1 => mkAppM ``Structural1222At #[cls,T]
  | 2 => mkAppM ``Theorem12213At #[cls,T]
  | 3 => mkAppM ``Theorem1222ModulesAt #[cls,T]
  | _ => throwError "Unsupported marker domain {t}"
private meta partial def literalMarkerBinder (type : Expr) : Bool :=
  match type with
  | .forallE _ domain body _ => (kind domain).isSome || literalMarkerBinder body
  | _ => false
private meta def hasMarkerBinder (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs _ => do
    for x in xs do
      if (kind (← inferType x)).isSome then return true
    return false

set_option maxHeartbeats 1000000 in
mutual
private meta partial def specialize (n : Name) : MetaM Name := withoutExporting <| withLCtx {} {} do
  let nn := mkPrivateName (← getEnv) (`Section09Localized ++ n)
  if (← getEnv).contains nn then return nn
  unless scopeOK n do throwError "Outside original Section08/09 source cone: {n}"
  let ci ← getConstInfo n
  unless ← hasMarkerBinder ci.type do throwError "No exact marker binder: {n}"
  let expected ← binders true #[] ci.type
  if n == ``CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.nonabelian_caseFive_impossible then
    let repl ← specialize ``CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.nonabelian_caseFive_impossible_of_original_rows
    let value := mkConst repl (ci.levelParams.map Level.param)
    unless ← isDefEq (← inferType value) expected do
      throwError "Original CaseFive replacement fails exact transformed-type check"
    return repl
  let some value := ci.value? true | throwError "No compiled body: {n}"
  let value ← binders false #[] value
  let actual ← inferType value
  unless ← isDefEq actual expected do
    throwError "Specialized type mismatch {n}\nActual: {actual}\nExpected: {expected}"
  if expected.hasFVar || value.hasFVar || expected.hasMVar || value.hasMVar then
    throwError "Open specialized expression: {n}"
  if expected.getUsedConstants.any oldNames.contains || value.getUsedConstants.any oldNames.contains then
    throwError "Original universal marker survived: {n}"
  unless ← isProp expected do throwError "Non-theorem clone requires explicit review: {n}"
  checkWithKernel value
  addDecl (.thmDecl {name:=nn,levelParams:=ci.levelParams,type:=expected,value:=value})
  liftM <| IO.println s!"CLONED {n} AS {nn}"
  return nn

private meta partial def binders (isType : Bool) (changed : Array (FVarId × Nat)) (e : Expr) : MetaM Expr := do
  let e ← if isType then whnf e else pure e
  let binder := match e with
    | .forallE n t b bi => if isType then some (n,t,b,bi) else none
    | .lam n t b bi => if !isType then some (n,t,b,bi) else none
    | _ => none
  if let some (n,t,b,bi) := binder then
    if let some k := kind t then
      if k == 4 then
        unless t.getAppArgs.size == 2 do
          throwError "Only original NaturalReduction4 may be removed"
        unless ← isDefEq t.getAppArgs[1]! (mkNatLit 4) do
          throwError "Only the degree-four reduction binder may be removed"
        return ← withLocalDecl n bi t fun x => binders isType (changed.push (x.fvarId!,k)) (b.instantiate1 x)
      let t ← narrowType t k
      return ← withLocalDecl n bi t fun x => do
        let body ← binders isType (changed.push (x.fvarId!,k)) (b.instantiate1 x)
        if isType then mkForallFVars #[x] body else mkLambdaFVars #[x] body
    let t ← rewrite changed t
    withLocalDecl n bi t fun x => do
      let body ← binders isType changed (b.instantiate1 x)
      if isType then mkForallFVars #[x] body else mkLambdaFVars #[x] body
  else rewrite changed e

private meta partial def applyLocal (changed : Array (FVarId × Nat)) (base : Expr)
    (k : Nat) (args : Array Expr) : MetaM Expr := do
  if args.isEmpty then return base
  unless args.size ≥ 4 do throwError "Partially applied old universal source: {base} {args}"
  let tp ← inferType base
  let ts := tp.getAppArgs
  unless (localKind tp).isSome && ts.size == 5 do throwError "Unexpected local source type {tp}"
  let ambientArgs := #[ts[0]!,ts[1]!,ts[2]!,ts[4]!]
  for i in [:4] do
    let a ← rewrite changed args[i]!
    unless ← isDefEq a ambientArgs[i]! do
      throwError "Original source ambient/Sylow mismatch at {i}: {a} versus {ambientArgs[i]!}"
  let mut rest := args.extract 4 args.size
  if k == 3 then
    unless rest.size ≥ 3 do throwError "Partial many-guard module application"
    rest := rest[:2].toArray ++ rest[3:].toArray
  return mkAppN base (← rest.mapM (rewrite changed))

private meta partial def rewrite (changed : Array (FVarId × Nat)) (e : Expr) : MetaM Expr := do
  if !(e.find? fun x => x.isFVar && changed.any (fun p => p.1 == x.fvarId!)).isSome then
    return e
  let f := e.getAppFn
  let args := e.getAppArgs
  if let .const n _ := f then
    let ats := #[``Structural1222.at, ``Theorem12213.at, ``Theorem1222ModulesOfMany.at]
    if let some ak := ats.findIdx? (· == n) then
      let cut := if ak == 2 then 7 else 6
      unless args.size ≥ cut do throwError "Partial original At adapter {n}"
      let base ← rewrite changed args[4]!
      let tp ← inferType base
      let ts := tp.getAppArgs
      unless localKind tp == some (ak + 1) && ts.size == 5 do
        throwError "Unexpected narrowed At input {n}: {tp}"
      for j in [:4] do
        unless ← isDefEq (← rewrite changed args[j]!) ts[j]! do
          throwError "At adapter changes original ambient group/class {n}"
      unless ← isDefEq (← rewrite changed args[5]!) ts[4]! do
        throwError "At adapter changes original Sylow {n}"
      return mkAppN base (← (args.extract cut args.size).mapM (rewrite changed))
    if let some i := fields.findIdx? (· == n) then
      unless args.size ≥ 2 do throwError "Bare original earlier projection {n}"
      let rec ← rewrite changed args[1]!
      let base ← mkAppM localFields[i]! #[rec]
      let rest := args.extract 2 args.size
      if i == 1 then return mkAppN base (← rest.mapM (rewrite changed))
      else return ← applyLocal changed base (if i == 0 then 1 else 2) rest
  if let .proj n i rec := f then
    if n == ``EarlierSetupResults then
      let rec ← rewrite changed rec
      let base ← mkAppM localFields[i]! #[rec]
      if i == 1 then return mkAppN base (← args.mapM (rewrite changed))
      else return ← applyLocal changed base (if i == 0 then 1 else 2) args
  if f.isFVar then
    if let some (_,k) := changed.find? (fun p => p.1 == f.fvarId!) then
      if k == 4 then throwError "Direct use of removed NaturalReduction4"
      if k != 0 then return ← applyLocal changed f k args
  if let .const n ls := f then
    let ci ← getConstInfo n
    if ← hasMarkerBinder ci.type then
      if !literalMarkerBinder ci.type then
        unless scopeOK n do throwError "Aliased source outside original cone: {n}"
        let some value := ci.value? true | throwError "No compiled aliased source: {n}"
        let value := value.instantiateLevelParams ci.levelParams ls
        liftM <| IO.println s!"INLINE_SOURCE {n}"
        return ← rewrite changed (mkAppN value args).headBeta
      let nn ← specialize n
      let kept ← forallTelescopeReducing ci.type fun xs _ => do
        let mut result := #[]
        for i in [:args.size] do
          if i < xs.size then
            if kind (← inferType xs[i]!) == some 4 then continue
          result := result.push (← rewrite changed args[i]!)
        return result
      return mkAppN (.const nn ls) kept
  match e with
  | .app f a => return .app (← rewrite changed f) (← rewrite changed a)
  | .lam n t b bi =>
    let t ← rewrite changed t
    withLocalDecl n bi t fun x => do
      mkLambdaFVars #[x] (← rewrite changed (b.instantiate1 x))
  | .forallE n t b bi =>
    let t ← rewrite changed t
    withLocalDecl n bi t fun x => do
      mkForallFVars #[x] (← rewrite changed (b.instantiate1 x))
  | .letE n t v b _ =>
    let t ← rewrite changed t
    let v ← rewrite changed v
    withLetDecl n t v fun x => do
      mkLetFVars #[x] (← rewrite changed (b.instantiate1 x))
  | .mdata md b => return .mdata md (← rewrite changed b)
  | .proj n i b => return .proj n i (← rewrite changed b)
  | _ => return e
end

set_option maxRecDepth 8192 in
set_option maxHeartbeats 30000000 in
run_cmd do
  liftTermElabM do
    discard <| specialize ``CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.point_span_abelian_of_original
    discard <| specialize ``CFSG.Quasithin.Chapter12.Section09.NaturalSource.abelian_contradiction
end CFSG.Quasithin.Chapter12.Section09.SourceAt.Localized

elab "local_section09% " n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let nn := mkPrivateName (← getEnv) (`Section09Localized ++ name)
  unless (← getEnv).contains nn do throwError "Source endpoint was not specialized: {name}"
  mkConstWithFreshMVarLevels nn

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section09.SourceAt
open Section02 Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The original point span is abelian from the earlier sources at this same G,T. -/
theorem point_span_abelian_from_source
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V n) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    IsMulCommutative F.U := by
  exact (local_section09% NaturalSource.Components.point_span_abelian_of_original)
    modules h hn preferred
    ⟨structural, CFSG.Quasithin.Chapter12.Section09.SourceAt.Localized.knownUniqueness, previous⟩ F g hgP hgH

/-- The original abelian natural branch reaches its terminal contradiction using local earlier sources. -/
theorem abelian_contradiction_from_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) : False := by
  exact (local_section09% NaturalSource.abelian_contradiction) h hn
    ⟨structural, CFSG.Quasithin.Chapter12.Section09.SourceAt.Localized.knownUniqueness, previous⟩ F hab

end CFSG.Quasithin.Chapter12.Section09.SourceAt
