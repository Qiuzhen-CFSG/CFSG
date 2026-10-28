module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTernaryInner
public import Theory.GroupTheory.CoreCentralNormalizerAction.QuinticInnerSubgroup

/-!
# The original quintic subgroup inside its ternary central carrier

The subgroup is the literal inverse image of the whole original action
under conjugation on (K/O₂(K))/Z. Its Sylow marking is the actual image of
T∩K under the original core-central projection. Two-perfectness, solvability,
the quotient of order five and the normalized product order are all derived
from the original source hypotheses. No substitute actor or Sylow is used.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The whole original quintic action becomes an actual subgroup of the
same ternary carrier, normalized by the actual projected component Sylow. -/
theorem original_hermitian_quintic_ternary_subgroup
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hc : IsPSLSign (coreCentralQuotient K) unitary 3 p) :
    let C := coreCentralQuotient K
    let Y := (coreCentralActorImage K (quinticResidual T L)).comap
      (MulAut.conj : C →* MulAut C)
    Y.map MulAut.conj = coreCentralActorImage K (quinticResidual T L) ∧
      IsPPerfect 2 Y ∧ Group.IsSolvable Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 5 ∧
      ∃ S : Sylow 2 C,
        (S : Subgroup C) = coreCentralIntersectionImage K (T : Subgroup G) ∧
        (S : Subgroup C) ≤ normalizer (Y : Set C) ∧
        ∃ a : ℕ, Nat.card (Y ⊔ (S : Subgroup C) : Subgroup C) = 2^a * 5 := by
  let := hq
  let C := coreCentralQuotient K
  let X := quinticResidual T L
  have hi := h.rankOneInput hout
  let : Group.IsSolvable (localBorel T L) :=
    localBorel_isSolvable hi.exponent hi.linear hi.sylow_normalizes
  have hXB : X ≤ localBorel T L := map_subtype_le _
  have hsolv : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hXB)
  have hXN : X ≤ normalizer (K : Set G) :=
    original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) M₁ :=
    ⟨T.subtype hTM₁,map_subgroupOf_eq_of_le hTM₁⟩
  obtain ⟨U,hU⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hK.1 hK.2.subnormal
  have hUK : (U : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hU,subgroupOf_map_subtype]
  have hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G) := by
    rw [hU]
    exact inf_le_left.trans (sylow_normalizes_quinticResidual hi.sylow_normalizes)
  obtain ⟨D,hD,_,hDX,_,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have hDimage := original_hermitian_quintic_central_image_card
    h hout hm hM₁ hCM₁ hK hnot hq D hD hDX
  have h5 : 5 ∣ Nat.card (coreCentralActorImage K X) := hDimage ▸
    card_dvd_of_le (map_mono (subgroupOf_mono (normalizer (K : Set G)) hDX))
  have hz : center C = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot (K ⧸ pCore 2 K)
  have hinner : coreCentralActorImage K X ≤ MulAut.innerSubgroup C := by
    cases unitary with
    | false =>
      exact original_hermitian_quintic_odd_linear_three_inner
        h hout hm hM₁ hCM₁ hK hq p hp ho hc
    | true =>
      exact original_hermitian_quintic_odd_unitary_three_inner
        h hout hm hM₁ hCM₁ hK hq p hp ho hc
  have hh := coreCentral_inner_quintic_subgroup K X U hUX hXN
    (quinticResidual_twoPerfect T L) hsolv
    (original_hermitian_quintic_core_quotient h hout hm).2 h5 hz hinner
  simpa only [hUK,coreCentralIntersectionImage] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
