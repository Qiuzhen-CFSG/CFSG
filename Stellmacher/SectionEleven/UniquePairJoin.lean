module

public import Stellmacher.SectionFiveToSeven.GeneratedPairHypotheses
public import Stellmacher.OmegaOneCenterMap

/-!
# The unique pair inside its generated subgroup

Under ambient Hypothesis Two and `S ≠ S0`, the restricted pair satisfies
Section Seven's genuine hypotheses, and its Sylow omega-center is nonnormal
in both members. These are the inputs to the unique-pair critical-path
argument. Hypothesis Two remains on the original ambient group: this theorem
does not assert that its global two-local conditions or alternative (c) are
hereditary, nor that the restricted S is Sylow in the generated group.
Together with the ambient hypothesis, the result supplies the local inputs of
`Later.GeneratedSectionEightContext`, whose adapter retains the required
(6.3) consequences without transferring the full hypothesis record.

The Section Seven transfer is `HypothesisTwo.generatedSectionSevenHypotheses`.
Alternative (5.1)(c) supplies the two ambient nonnormalities, since the other
alternatives require `S = S0`. The injective omega-center map identifies the
restricted omega-center, and the normalizer restriction identity proves that
normality inside either local member is unchanged by the ambient restriction.

Source: Stellmacher (5.1)(c), the opening of Section Seven, and the unique
maximal two-local branch in Section Eleven, `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven

universe u

private theorem omega_restrict
    {H : Type u} [Group H] (S J : Subgroup H) (hSJ : S ≤ J) :
    omegaOneCenter (S.subgroupOf J) = (omegaOneCenter S).subgroupOf J := by
  apply Subgroup.map_injective J.subtype_injective
  have hOmega : omegaOneCenter S ≤ J :=
    (Subgroup.map_subtype_le _).trans hSJ
  rw [Subgroup.map_subgroupOf_eq_of_le hOmega]
  change (omegaOneCenterAmbient (S.subgroupOf J)).map J.subtype =
    omegaOneCenterAmbient S
  rw [← omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hSJ]

private theorem normal_restrict_iff
    {H : Type u} [Group H] (A P J : Subgroup H)
    (hAP : A ≤ P) (hPJ : P ≤ J) :
    NormalIn (A.subgroupOf J) (P.subgroupOf J) ↔ NormalIn A P := by
  have hrestricted : A.subgroupOf J ≤ P.subgroupOf J :=
    Subgroup.comap_mono hAP
  simp only [NormalIn, hrestricted, hAP, true_and,
    Subgroup.normal_subgroupOf_iff_le_normalizer hrestricted,
    Subgroup.normal_subgroupOf_iff_le_normalizer hAP]
  rw [← Subgroup.subgroupOf_normalizer_eq (hAP.trans hPJ)]
  constructor
  · intro hnormal element helement
    exact hnormal (show (⟨element, hPJ helement⟩ : J) ∈ P.subgroupOf J from helement)
  · exact Subgroup.comap_mono

/-- The source-faithful join hypotheses for the unique pair: Section Seven
and both nonnormal omega-centers, retaining Hypothesis Two on H rather than
asserting it anew on the join. -/
public theorem unique_pair_join_hypothesis
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hne : S ≠ (S0 : Subgroup H)) :
    SectionSevenHypotheses (P1 ⊔ P2 : Subgroup H)
      (S.subgroupOf (P1 ⊔ P2)) (P1.subgroupOf (P1 ⊔ P2))
      (P2.subgroupOf (P1 ⊔ P2)) ∧
    ¬ NormalIn (omegaOneCenter (S.subgroupOf (P1 ⊔ P2)))
      (P1.subgroupOf (P1 ⊔ P2)) ∧
    ¬ NormalIn (omegaOneCenter (S.subgroupOf (P1 ⊔ P2)))
      (P2.subgroupOf (P1 ⊔ P2)) := by
  refine ⟨h.generatedSectionSevenHypotheses, ?_⟩
  have hSP1 : S ≤ P1 := h.fiveOne.P1_mem.1.2.1.1
  have hSP2 : S ≤ P2 := h.fiveOne.P2_mem.1.2.1.1
  have hOmega : omegaOneCenter S ≤ S := Subgroup.map_subtype_le _
  rw [omega_restrict S (P1 ⊔ P2) (hSP1.trans le_sup_left),
    normal_restrict_iff _ _ _ (hOmega.trans hSP1) le_sup_left,
    normal_restrict_iff _ _ _ (hOmega.trans hSP2) le_sup_right]
  cases h.fiveOne.alternative with
  | a heq _ _ => exact (hne heq).elim
  | b heq _ => exact (hne heq).elim
  | c _ _ _ hleft hright _ _ _ _ _ _ _ _ => exact ⟨hleft, hright⟩

end Stellmacher.SectionEleven
