module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.RemainingBranch
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CharacteristicVertex
public import Theory.SpecificGroups.SymmetricFourResidualCore

/-!
# The single-component branch at common Sylow order eight

A characteristic-two vertex is S₄, whose two-core lies in its two-residual.
If a component contains this residual and the other residual escapes, F.6.7
places that core in the opposite vertex core. Both cores have order four,
so they coincide and form a nontrivial common normal subgroup. This contradicts
the trivial ambient two-core. Thus the selected component vertex is exceptional,
without the general F.6.13 recognition theorem.

Source: Aschbacher–Smith, F.6.7, F.6.13 and F.6.17–18, pp.305,307,309–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}
private theorem core_four (h : IsGoldschmidtTriple G₁ G₂)
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

theorem SingleResidualComponent.left_exceptional_of_intersection_eight
    (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8) :
    generalizedFitting G₁ ≠ pCore 2 G₁ := by
  intro hg
  obtain ⟨e⟩ := h.local_equiv_symmetric_four_of_intersection_card_eight hg hT
  let Q₁ := (pCore 2 G₁).map G₁.subtype
  let Q₂ := (pCore 2 G₂).map G₂.subtype
  have hQK : Q₁ ≤ d.component :=
    (map_mono (Theory.SpecificGroups.SymmetricFour.twoCore_le_twoResidual_of_equiv e)).trans
      d.left_contains
  have hi := (h.right_subnormal_core_iff_not_residual_le d.component
    d.isComponent.1).mpr d.right_escapes
  have hle : Q₁ ≤ Q₂ :=
    (le_inf (h.local_twoCore_le_intersection.trans inf_le_right) hQK).trans hi
  have hc₁ : Nat.card Q₁ = 4 := core_four h hT
  have hc₂ : Nat.card Q₂ = 4 := core_four h.symm (by simpa only [inf_comm] using hT)
  have he : Q₁ = Q₂ := eq_of_le_of_card_ge hle (by rw [hc₁,hc₂])
  have hbot : Q₁ = ⊥ := by
    apply h.common_normal_eq_bot hcore Q₁ h.local_twoCore_le_intersection
    · exact (normal_subgroupOf_iff_le_normalizer
        (h.local_twoCore_le_intersection.trans inf_le_left)).mpr h.left_core_normalized
    · apply (normal_subgroupOf_iff_le_normalizer
        (h.local_twoCore_le_intersection.trans inf_le_right)).mpr
      change G₂ ≤ normalizer (Q₁ : Set G)
      rw [he]
      exact h.symm.left_core_normalized
  rw [hbot,card_bot] at hc₁
  norm_num at hc₁

/-- Every source common Sylow of order eight has the actual dihedral model. -/
theorem dihedral_intersection_of_card_eight
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8) :
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) := by
  by_cases hg₁ : generalizedFitting G₁ = pCore 2 G₁
  · exact h.intersection_equiv_dihedral_four_of_characteristic_two hg₁ hT
  by_cases hg₂ : generalizedFitting G₂ = pCore 2 G₂
  · obtain ⟨e⟩ := h.symm.intersection_equiv_dihedral_four_of_characteristic_two hg₂
      (by simpa only [inf_comm] using hT)
    exact ⟨(MulEquiv.subgroupCongr (inf_comm _ _)).trans e⟩
  have hc := h.intersection_card_of_neither_characteristic_two hcore hg₁ hg₂
  omega

end CFSG.Quasithin.ChapterF.SourceAssembly
