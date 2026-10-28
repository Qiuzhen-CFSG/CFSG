module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.Contradiction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.NaturalDualBestRank

/-!
# Discharging the natural-plus-dual rank input in the extraspecial contradiction

The original extraspecial route now consumes the proved rank-four theorem
for best offenders on the literal PSL₄(2) natural-plus-dual representation.
All other earlier source implications, groups, quotient actions and plane
markings remain those of the original 15.3.49 construction.

Source: Aschbacher--Smith, 15.3.49, printed pp.1142--1145, and
B.4.9(2)(iii), printed p.92 (`refs/quasithin.pdf`).
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup ComponentReduction ModelReduction BinaryModels ReducedModels
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative commutatorElement

universe u v
variable {G : Type u} [Group G] [Finite G]
namespace EarlierLocal

/-- The original extraspecial contradiction with its concrete B.4.9 rank input discharged. -/
theorem false_of_earlier_of_naturalDualRank
    {κ : GroupClass.{u}} (T : Sylow 2 G) (M Y Y0 ZS upper : Subgroup G)
    [IsElementaryAbelian 2 (localModule T M)]
    (a : Section03.NaturalOrthogonalAction M (localModule T M))
    (o : FusionCore.NaturalOrthogonalAction M (localModule T M))
    (i : OrthogonalPlaneIndex)
    (d : EarlierLocal κ M Y (localModule T M) Y0 ZS (centralInvolutions T) upper T)
    (hseed : ZS = fixedPlane (localModule T M) (planeStabilizer T (a.plane i)))
    (hseed_comm : ⁅ZS, (T : Subgroup G)⁆ ≤ centralInvolutions T)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hnormalizer : ∀ W : Subgroup G, W ≤ localModule T M →
      ¬ IsTotallySingular o.form W → normalizer (W : Set G) ≤ M)
    (hlocal : ∀ H : Subgroup G, H ∈ outsideFamily Y0 (T : Subgroup G) M → H ≤ upper →
      centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (h48 : ∀ H : Subgroup G, H ∈ outsideFamily Y0 (T : Subgroup G) M → H ≤ upper →
      localSpan (ZS.subgroupOf H) ⊤ ≤ pCore 2 H ∧
      (frattini (localSpan (ZS.subgroupOf H) ⊤)).map
        (localSpan (ZS.subgroupOf H) ⊤).subtype ≤ (centralInvolutions T).subgroupOf H ∧
      (∀ h : H, (∀ u ∈ localSpan (ZS.subgroupOf H) ⊤,
        ⁅u,h⁆ ∈ (centralInvolutions T).subgroupOf H) ↔ h ∈ pCore 2 H) ∧
      ⁅localSpan ZS H, localTwoCore H⁆ ≤ centralInvolutions T)
    (ι : Subgroup G → Type v) [∀ H, Finite (ι H)]
    (geometry : ∀ H : Subgroup G, H ∈ outsideFamily Y0 (T : Subgroup G) M →
      (hHU : H ≤ upper) →
      letI := d.elementary_seed H hHU
      letI := d.elementary_span H hHU
      Nonempty (GeometricFamily (ι H) Y (T : Subgroup G) H (localModule T M) ZS
        (centralInvolutions T)))
    (classification : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (splitting : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u}) : False := by
  exact false_of_earlier T M Y Y0 ZS upper a o i d hseed hseed_comm hempty
    hnormalizer hlocal h48 ι geometry classification sections orbits source splitting
    ModelExclusions.MiddleEight.naturalDualBestRank

end EarlierLocal
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
