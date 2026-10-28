module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.LinearParameters
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CharacteristicVertex
public import Theory.SpecificGroups.SymmetricFourResidualCore

/-!
# A proper component with Sylow order four forces a mixed local pair

At common Sylow order eight a characteristic-two vertex is S4, so its
four-group core lies in its two-residual. If both vertices had this form,
both cores would equal the original residual's Sylow four-group. Their
common normal subgroup would contradict trivial ambient two-core.
Neither vertex can fail characteristic two simultaneously, since that
would force the common Sylow order to be at most four. Thus the proper
PSL2 component branch has precisely one characteristic-two vertex.

Source: Aschbacher--Smith F.6.18(5), printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem local_core_card_four (h : IsGoldschmidtTriple G₁ G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8) :
    Nat.card ((pCore 2 G₁).map G₁.subtype) = 4 := by
  let Q := (pCore 2 G₁).map G₁.subtype
  let R := Q.subgroupOf (G₁ ⊓ G₂)
  have hi : R.index = 2 := h.left_core_index
  have hc := R.index_mul_card
  rw [hi, hT] at hc
  have hR : Nat.card R = 4 := by omega
  rw [← Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv]
  exact hR

/-- A Sylow four-group in the original two-residual excludes two good vertices. -/
theorem not_both_characteristic_two_of_residual_sylow_four
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (P : Sylow 2 (pResidual 2 G)) (hP : Nat.card P = 4) :
    ¬ (generalizedFitting G₁ = pCore 2 G₁ ∧ generalizedFitting G₂ = pCore 2 G₂) := by
  rintro ⟨hg₁, hg₂⟩
  obtain ⟨e₁⟩ := h.local_equiv_symmetric_four_of_intersection_card_eight hg₁ hT
  obtain ⟨e₂⟩ := h.symm.local_equiv_symmetric_four_of_intersection_card_eight hg₂
    (by simpa only [inf_comm G₂ G₁] using hT)
  let R := pResidual 2 G
  let U := (G₁ ⊓ G₂) ⊓ R
  obtain ⟨S, hS⟩ := h.subnormal_intersection_sylow R
    (inferInstance : R.Normal).isSubnormal
  have hU : Nat.card U = 4 := by
    have hh : (S : Subgroup R).map R.subtype = U := by
      rw [hS, subgroupOf_map_subtype]
    rw [← hh, card_map_of_injective R.subtype_injective]
    exact (Nat.card_congr (S.equiv P).toEquiv).trans hP
  let Q₁ := (pCore 2 G₁).map G₁.subtype
  let Q₂ := (pCore 2 G₂).map G₂.subtype
  have hQ₁ : Q₁ = U := by
    apply eq_of_le_of_card_ge
    · exact le_inf h.local_twoCore_le_intersection
        ((map_mono (Theory.SpecificGroups.SymmetricFour.twoCore_le_twoResidual_of_equiv e₁)).trans
          (map_pResidual_le 2 G₁.subtype))
    · rw [hU, local_core_card_four h hT]
  have hQ₂ : Q₂ = U := by
    apply eq_of_le_of_card_ge
    · exact le_inf (by simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection)
        ((map_mono (Theory.SpecificGroups.SymmetricFour.twoCore_le_twoResidual_of_equiv e₂)).trans
          (map_pResidual_le 2 G₂.subtype))
    · rw [hU, local_core_card_four h.symm (by simpa only [inf_comm G₂ G₁] using hT)]
  have hbot : U = ⊥ := by
    apply h.common_normal_eq_bot hcore U inf_le_left
    · apply (normal_subgroupOf_iff_le_normalizer (inf_le_left.trans inf_le_left)).mpr
      change G₁ ≤ normalizer (U : Set G)
      rw [← hQ₁]
      exact h.left_core_normalized
    · apply (normal_subgroupOf_iff_le_normalizer (inf_le_left.trans inf_le_right)).mpr
      change G₂ ≤ normalizer (U : Set G)
      rw [← hQ₂]
      exact h.symm.left_core_normalized
  rw [hbot, card_bot] at hU
  norm_num at hU

/-- The actual residual-Sylow hypothesis supplies the mixed branch of the
exceptional amalgam theorem, with its original vertex orientation. -/
theorem mixed_vertices_of_residual_sylow_four
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (P : Sylow 2 (pResidual 2 G)) (hP : Nat.card P = 4) :
    (generalizedFitting G₁ = pCore 2 G₁ ∧ generalizedFitting G₂ ≠ pCore 2 G₂) ∨
    (generalizedFitting G₂ = pCore 2 G₂ ∧ generalizedFitting G₁ ≠ pCore 2 G₁) := by
  by_cases hg₁ : generalizedFitting G₁ = pCore 2 G₁
  · exact .inl ⟨hg₁, fun hg₂ =>
      not_both_characteristic_two_of_residual_sylow_four h hcore hT P hP ⟨hg₁, hg₂⟩⟩
  · by_cases hg₂ : generalizedFitting G₂ = pCore 2 G₂
    · exact .inr ⟨hg₂, hg₁⟩
    · have hh := h.intersection_card_of_neither_characteristic_two hcore hg₁ hg₂
      omega

/-- Apply the mixed-vertex result to the actual proper PSL2 residual
constructed by the dihedral component sieve. -/
theorem mixed_vertices_of_proper_psl_residual
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (hproper : pResidual 2 G ≠ ⊤) {p f : ℕ}
    (hp : p.Prime) (ho : Odd p) (hf : 1 ≤ f)
    (hm : ClassicalGroup.IsPSL (pResidual 2 G) 2 (p ^ f)) :
    (generalizedFitting G₁ = pCore 2 G₁ ∧ generalizedFitting G₂ ≠ pCore 2 G₂) ∨
    (generalizedFitting G₂ = pCore 2 G₂ ∧ generalizedFitting G₁ ≠ pCore 2 G₁) := by
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  obtain ⟨T, hTs⟩ := h.intersection_sylow
  have hTc : Nat.card T = 8 := by simpa only [hTs] using hT
  let P : Sylow 2 (pResidual 2 G) := default
  let S := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let a : P ≃* S := (P : Subgroup (pResidual 2 G)).equivMapOfInjective
    j.toMonoidHom j.injective
  have hS := (sylow_card_section_le T (pResidual 2 G) j.toMonoidHom j.surjective S).trans hTc.le
  rcases Theory.ClassicalSmallSylow.psl2_small_sylow_parameters
    ⟨p, f, hp, ho, by omega, hF⟩ S hS with ⟨hS4, _⟩ | ⟨hS8, _⟩
  · exact mixed_vertices_of_residual_sylow_four h hcore hT P
      ((Nat.card_congr a.toEquiv).trans hS4)
  · have h8 : 8 ∣ Nat.card (pResidual 2 G) := by
      rw [Nat.card_congr j.toEquiv, ← hS8]
      exact S.card_subgroup_dvd_card
    exact (hproper (normal_eq_top_of_sylow_eight_of_eight_dvd T hTc (pResidual 2 G)
      (isPGroup_quotient_pResidual 2) h8)).elim

end CFSG.Quasithin.ChapterF.SourceAssembly
