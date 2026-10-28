module
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ActionCentralizer
import all CFSG.Quasithin.Chapter13.Section05.A5Source.BlockApplication
import all CFSG.Quasithin.Chapter13.Section05.A5Source.BlockMarking
import all CFSG.Quasithin.Chapter13.Section05.A5Source.CentralCoverNormalizer
import all CFSG.Quasithin.Chapter13.Section05.A5Source.CentralQuotient
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefActions
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefCatalogue
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefCount
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefSieveApplication
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ChiefSieveComplete
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ClassifiedChiefActions
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentAction
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentActionComplete
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentConfiguration
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentSelection
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentStructure
import all CFSG.Quasithin.Chapter13.Section05.A5Source.EightOrders
import all CFSG.Quasithin.Chapter13.Section05.A5Source.Elimination
import all CFSG.Quasithin.Chapter13.Section05.A5Source.FittingAction
import all CFSG.Quasithin.Chapter13.Section05.A5Source.FullConfiguration
import all CFSG.Quasithin.Chapter13.Section05.A5Source.G2False
import all CFSG.Quasithin.Chapter13.Section05.A5Source.LocalContainment
import all CFSG.Quasithin.Chapter13.Section05.A5Source.MarkedChiefActions
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ModelContainment
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NaturalExclusion
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBNPair
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalClosure
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalCore
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledAmalgam
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledCompletion
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledIntersection
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledPlane
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledPlaneRestriction
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledPoint
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledUpgrade
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalMaximal
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrders
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrdinaryAmalgam
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrdinaryEndpoints
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrdinaryRecognition
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPair
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPairCompletion
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPlaneModel
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPlaneUnitary
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointCentralizer
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointComparison
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointSplit
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointStructure
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointSwap
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointUnitary
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalRecognition
import all CFSG.Quasithin.Chapter13.Section05.A5Source.NormalSylow
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ParabolicApplication
import all CFSG.Quasithin.Chapter13.Section05.A5Source.PlaneApplication
import all CFSG.Quasithin.Chapter13.Section05.A5Source.PlaneControl
import all CFSG.Quasithin.Chapter13.Section05.A5Source.ResidualStructure
import all CFSG.Quasithin.Chapter13.Section05.A5Source.SeedNormalizer
import all CFSG.Quasithin.Chapter13.Section05.A5Source.SixFalse
import all CFSG.Quasithin.Chapter13.Section05.A5Source.SourceF9
import all CFSG.Quasithin.Chapter13.Section05.A5Source.SourceGeometry
import all CFSG.Quasithin.Chapter13.Section05.A5Source.SourceRecognition
import all CFSG.Quasithin.Chapter13.Section05.A5Source.UnitaryChiefExclusion
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SourceRecognition
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SeedKnownSimple
meta import Lean.Elab.Tactic

/-!
# Original nonabelian A₅ recognition over the complete catalogue

The only embedding input used in the source A₅ recognition family is the
common-normal theorem in seed-centralizer control. `SeedKnownSimple` proves
that control from the original context and the complete known-simple
catalogue. Substituting its two seed theorems therefore proves the original
ambient model conclusion without a full A.3.12 embedding hypothesis.

The internal `import all` edges are intentional: this extension specializes
the existing proof bodies while preserving their public interfaces. A local
elaborator replaces the two seed leaves and retains shared private lemmas;
every resulting theorem and definition is checked by Lean's kernel. No
assumed embedding theorem is introduced. The internal specialization machinery
is not part of the public API.

Source: Aschbacher–Smith 13.2.3, 13.5.7–25, printed pp.879,917–925.
-/

open Lean Meta Elab Tactic

meta def seedReplacement (n : Name) : Option Name :=
  if n == ``CFSG.Quasithin.Chapter13.Section05.A5Source.Context.seed_normalizer then
    some ``CFSG.Quasithin.Chapter13.Section05.A5Source.Context.seed_normalizer_knownSimple
  else if n == ``CFSG.Quasithin.Chapter13.Section05.A5Source.Context.seed_centralizer then
    some ``CFSG.Quasithin.Chapter13.Section05.A5Source.Context.seed_centralizer_knownSimple
  else none

mutual
meta partial def specializedSource (ownerName n : Name) : MetaM Name := withoutExporting do
  if let some nn := seedReplacement n then return nn
  let nn := mkPrivateName (← getEnv) (ownerName ++ `specialization ++ n)
  if (← getEnv).contains nn then return nn
  let ci ← getConstInfo n
  let some v := ci.value? true | throwError "No body available for {n}"
  let p ← specializeBinders ownerName none v
  let t ← inferType p
  if p.hasFVar || t.hasFVar then throwError "Remaining free variable in {n}"
  if ← isProp t then
    addDecl (.thmDecl { name := nn, levelParams := ci.levelParams, type := t, value := p })
  else
    addDecl (.defnDecl { name := nn, levelParams := ci.levelParams, type := t, value := p, hints := .opaque, safety := .safe })
  return nn

meta partial def specializeBinders (ownerName : Name) (bad : Option FVarId) (e : Expr) : MetaM Expr := do
  if let .lam n t b bi := e then
    if n == `hA312 then
      return ← withLocalDecl n bi t fun x => specializeBinders ownerName (some x.fvarId!) (b.instantiate1 x)
    let t ← if let some bad := bad then removeSourceInput ownerName bad t else pure t
    withLocalDecl n bi t fun x => do
      let b ← specializeBinders ownerName bad (b.instantiate1 x)
      mkLambdaFVars #[x] b
  else if let some bad := bad then removeSourceInput ownerName bad e
  else throwError "No hA312 argument"

meta partial def removeSourceInput (ownerName : Name) (bad : FVarId) (e : Expr) : MetaM Expr := do
  if !(e.find? fun x => x.isFVar && x.fvarId! == bad).isSome then return e
  let f := e.getAppFn
  let args := e.getAppArgs
  if let .const n ls := f then
    if args.any (fun x => x.isFVar && x.fvarId! == bad) then
      let nn ← specializedSource ownerName n
      return ← removeSourceInput ownerName bad (mkAppN (.const nn ls) (args.filter (fun x => !(x.isFVar && x.fvarId! == bad))))
  match e with
  | .app f a => return .app (← removeSourceInput ownerName bad f) (← removeSourceInput ownerName bad a)
  | .lam n t b bi => return .lam n (← removeSourceInput ownerName bad t) (← removeSourceInput ownerName bad b) bi
  | .forallE n t b bi => return .forallE n (← removeSourceInput ownerName bad t) (← removeSourceInput ownerName bad b) bi
  | .letE n t v b nc =>
    return .letE n (← removeSourceInput ownerName bad t) (← removeSourceInput ownerName bad v) (← removeSourceInput ownerName bad b) nc
  | .mdata md b => return .mdata md (← removeSourceInput ownerName bad b)
  | .proj n i b => return .proj n i (← removeSourceInput ownerName bad b)
  | _ => throwError "Unhandled dependency {e}"
end

elab "seed_specialization% " n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let some ownerName ← Term.getDeclName? | throwError "No current declaration"
  let nn ← specializedSource ownerName name
  mkConstWithFreshMVarLevels nn

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hH : H ∈ Section08.Source.Hz (Section06.TerminalContradiction.Ratio.residualCentralizer L V₁)
    (T : Subgroup G) (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Section08.Source.UH H V₃))

include d hH hU
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- The original nonabelian A₅ context has the degree-five ambient model conclusion. -/
theorem source_modelConclusion_knownSimple : ModelConclusion G 5 := by
  exact (seed_specialization% source_modelConclusion) (D := ⟨T,L,V,V₃,V₁,H⟩) d hH hU

end CFSG.Quasithin.Chapter13.Section05.A5Source
