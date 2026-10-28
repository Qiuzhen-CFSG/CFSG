module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOnePushingUpOrdinary
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrained
-- Internal continuation of the same chosen-module proof, sharing its residual data.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOnePushingUpOrdinary

/-!
# Constrained components on the original chosen orbit

The original residual and its covering quotient provide the surjection
used by the constrained exclusion in both marked families. Together with
the established unitary ordinary-component exclusion and the completed
ambient reciprocal escape, this proves unitary residual uniqueness.

Source: Aschbacher--Smith 4.2.5--13 and 4.4.6(2), pp.609--612,620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape Chapter7.NormalizedSource
open ChapterB ChapterE.Section06.FixedPointBounds ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem sourceOrbit_pushingUp_no_constrained_of_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hexp : ¬ ∀ P : Subgroup (D.orbitComponent ⧸ center D.orbitComponent),
      IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (hsize : 20160 < Nat.card (D.orbitComponent ⧸ center D.orbitComponent))
    (hl5 : ¬ Nat.card (D.orbitComponent ⧸ center D.orbitComponent) ∣ 9999360)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False := by
  obtain ⟨hn,_,_,⟨e⟩⟩ := D.sourceOrbit_pushingUp_residual_data h hmany hV hnon hw
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let := D.orbitComponent_quasisimple h.toHypothesis1221
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let π := e.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
    (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  exact no_constrained_normalized_rankOne hw.2.2.2.2.2.2.1 hn
    (Group.IsPerfect.not_isSolvable _) hexp π hπ hsize hl5 K hK hq hout hfK

/-- Every constrained component in the original unitary pair is impossible. -/
theorem sourceOrbit_unitary_pushingUp_no_constrained
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs : 2 ≤ s)
    (hu : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False :=
  D.sourceOrbit_pushingUp_no_constrained_of_model h hmany hV hnon
    (unitary_not_two_exponent hs hu) (unitary_card_gt_20160 hs hu)
    (unitary_card_not_dvd_linear_five_two hs hu) hw K hK hq hout hfK

/-- Every constrained component in the original Suzuki pair is impossible. -/
theorem sourceOrbit_suzuki_pushingUp_no_constrained
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {a : ℕ} (ha : 1 ≤ a)
    (es : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup a)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False :=
  D.sourceOrbit_pushingUp_no_constrained_of_model h hmany hV hnon
    (suzuki_not_two_exponent ha es) (suzuki_card_gt_20160 ha es)
    (suzuki_card_not_dvd_linear_five_two ha es) hw K hK hq hout hfK

/-- Failure of uniqueness contradicts both branches of the actual unitary escape. -/
theorem sourceOrbit_unitary_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hu : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) := by
  by_contra hnot
  obtain ⟨J,H,W,hw,K,hK,hq,hout,hfK,_⟩ :=
    D.sourceOrbit_unitary_pushingUp_constrained_of_not_unique
      h hmany hV hs hnm hnon hs2 hu A hne hA ho hnot
  exact D.sourceOrbit_unitary_pushingUp_no_constrained h hmany hV hnon hs2 hu hw K hK hq
    (fun hh => hout (hh.trans (subgroupOf_mono H inf_le_right))) hfK
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

end
