module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourMiddleStar
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Complete

/-!
# The remaining doubled-natural source arguments on the actual embeddings

The degree-four nonnormal branch now supplies the source middle-node
parabolic, with its precise star quotient map and arbitrary SL5(2) marking.
The remaining module argument needs only its Sylow-fixed omega-center
conclusion at that actual embedding. The ordinary J4 exclusion is retained.

In degree five, applying the checked pure-point family after nonsingular
control and positive zeroth closure gives all three original task outputs
from the J4 exclusion alone. This uses the source order of arguments and
constructs the permitted source model; no pure-point input is added.

J4, the degree-four fixed-space argument and the marked MS input retain
their existing source owners. These conditional assembly statements do not
assert the unresolved source theorem. Source: Aschbacher--Smith 12.1.1--7,
printed pp.788--792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Apply the actual middle-node embedding to the original centralizer and
zeroth-closure consumer, retaining only its outstanding module conclusion. -/
theorem doubleNatural_nonsingular_controls_of_jankoFour_middle_flag_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → False) →
    (n = 4 → ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w < K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        KernelConclusion K Q → OffenderConclusion K Q →
        ∀ (e : starImage K Q K ≃* BinaryLinear.OuterCyclic.LinearGroup 5)
          (b : BinaryLinear.FiveFlagGeometry.FiveBasis),
        ((starM K Q (B.localPointCentralizer w)).subgroupOf
          (starImage K Q K)).map e.toMonoidHom =
            BinaryLinear.FiveFlagGeometry.flagStabilizer b {0,3} →
        B.pointResidual w ≤ centralizer ((starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hj hp
  apply D.doubleNatural_nonsingular_controls_of_jankoFour_four_star_of_many h hmany B hj
  intro hn S w hw hc hnon hout Q K hKn hRK hi hk ho _ _ he _
  subst n
  obtain ⟨e₀⟩ := he
  let e := e₀.trans (BinaryLinear.OuterCyclic.slEquivLinear 5)
  obtain ⟨b,hb⟩ := D.doubleNatural_four_adapted_C27_middle h B S w hw K hKn hRK.le hi e
  exact hp rfl S w hw hc hnon hout K hKn hRK hi hk ho e b hb

/-- In degree five the ordinary J4 exclusion is the only remaining premise
for nonsingular control, pure intersection centralization and positive zeroth weak closure. -/
theorem doubleNatural_five_conclusions_of_jankoFour_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        8 ≤ primeRank 2 (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → False) →
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hj
  obtain ⟨hc,_,hw⟩ := D.doubleNatural_five_nonsingular_controls_of_jankoFour_of_many h hmany B hj
  obtain ⟨S⟩ := D.doubleNatural_sourceModel_of_many h hmany B
  have hp := D.doubleNatural_five_pure_conclusions_of_many h hmany B hw S hc
  exact ⟨hc,hp.2.2.2.2.2,hw⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
