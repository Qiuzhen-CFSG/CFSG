module

public import Theory.Representation.PSL3Two.FourGroupGeometry
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
/-!
# The point four-group normalizer in the full automorphism group

Conjugation identifies the point translations with an inner four-group. The
two marked translations exclude every graph automorphism from its normalizer
and locate each inner implementer in the full point parabolic, which is S₄.
The point core is normal in that parabolic. A checked two-generator centralizer
calculation gives kernel the four-group itself, hence conjugation image of
order six. In particular the normalizer is the full parabolic, not its A₄
residual.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the model
normalizer assertion used in 15.3.61(2), printed p.1151.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace BinaryLinearThree.FourGroupGeometry.Normalizers
abbrev innerPoint : Subgroup (MulAut SL) := pointV.map MulAut.conj

theorem conjugate_conj (α : MulAut SL) (g : SL) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  simp

private theorem translations_core : Bruhat.upper 1 ∈ pointV ∧ Bruhat.upper 2 ∈ pointV := by
  decide +kernel

private theorem pointV_normalizes : pointParabolicSL ≤ normalizer (pointV : Set SL) := by
  rw [← MarkedProduct.pointParabolic_core]
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact ⟨(⟨g,hg⟩ : pointParabolicSL) * y * (⟨g,hg⟩ : pointParabolicSL)⁻¹,
    (inferInstance : (pCore 2 pointParabolicSL).Normal).conj_mem y hy ⟨g,hg⟩, rfl⟩

theorem point_normalizer : normalizer (innerPoint : Set (MulAut SL)) =
    pointParabolicSL.map MulAut.conj := by
  apply le_antisymm
  · intro α hα
    have hm (a : SL) (ha : a ∈ pointV) : α a ∈ pointV := by
      have h := (mem_normalizer_iff.mp hα (MulAut.conj a)).mp
        (mem_map_of_mem MulAut.conj ha)
      rw [conjugate_conj] at h
      exact (mem_map_iff_mem conj_injective).mp h
    obtain ⟨g,rfl | rfl⟩ := inner_or_graph α
    · exact mem_map_of_mem _ (inner_preserving_test g
        (pointV_le (hm _ translations_core.1)) (pointV_le (hm _ translations_core.2)))
    · exact False.elim (outer_exclusion_test g
        ⟨pointV_le (hm _ translations_core.1),pointV_le (hm _ translations_core.2)⟩)
  · exact (map_mono pointV_normalizes).trans (pointV.le_normalizer_map MulAut.conj)

set_option maxRecDepth 10000 in
private theorem point_centralizer_test : ∀ g : SL,
    Bruhat.upper 1 * g = g * Bruhat.upper 1 →
    Bruhat.upper 2 * g = g * Bruhat.upper 2 → g ∈ pointV := by decide +kernel

private theorem pointV_comm (a b : pointV) : a * b = b * a := by
  have hi (x : pointV) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    simpa only [coe_mul, coe_one, pow_two] using pointV_square x x.property
  calc
    a * b = (a * b)⁻¹ := (hi _).symm
    _ = b * a := by rw [mul_inv_rev, hi, hi]

theorem point_centralizer : centralizer (innerPoint : Set (MulAut SL)) = innerPoint := by
  apply le_antisymm
  · intro α hα
    have hn := (centralizer_le_normalizer (innerPoint : Set (MulAut SL))) hα
    rw [point_normalizer] at hn
    obtain ⟨g,hg,rfl⟩ := hn
    apply mem_map_of_mem
    apply point_centralizer_test
    · apply MarkedAutomorphisms.conj_injective
      simpa only [map_mul] using
        (mem_centralizer_iff.mp hα _ (mem_map_of_mem MulAut.conj translations_core.1))
    · apply MarkedAutomorphisms.conj_injective
      simpa only [map_mul] using
        (mem_centralizer_iff.mp hα _ (mem_map_of_mem MulAut.conj translations_core.2))
  · rintro α ⟨g,hg,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro β ⟨h,hh,rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg MulAut.conj (congrArg Subtype.val (pointV_comm ⟨h,hh⟩ ⟨g,hg⟩))

noncomputable def pointNormalizerEquiv : normalizer (innerPoint : Set (MulAut SL)) ≃*
    Equiv.Perm (Fin 4) :=
  (MulEquiv.subgroupCongr point_normalizer).trans
    ((pointParabolicSL.equivMapOfInjective MulAut.conj conj_injective).symm.trans
      pointEquivSymmetric)

theorem point_action_card : Nat.card innerPoint.normalizerMonoidHom.range = 6 := by
  have hV : Nat.card innerPoint = 4 :=
    (Nat.card_congr (pointV.equivMapOfInjective MulAut.conj conj_injective).toEquiv).symm.trans
      card_pointV
  have hN : Nat.card (normalizer (innerPoint : Set (MulAut SL))) = 24 := by
    rw [Nat.card_congr pointNormalizerEquiv.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hK : Nat.card innerPoint.normalizerMonoidHom.ker = 4 := by
    rw [normalizerMonoidHom_ker, point_centralizer]
    exact (Nat.card_congr (subgroupOfEquivOfLe innerPoint.le_normalizer).toEquiv).trans hV
  rw [← innerPoint.normalizerMonoidHom.ker.card_mul_index, index_ker, hK] at hN
  omega
end BinaryLinearThree.FourGroupGeometry.Normalizers
