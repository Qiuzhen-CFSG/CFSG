module

public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Operators
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# Order-four conjugacy on the hexacode over F₄

Every order-four linear automorphism of the actual three-dimensional hexacode
is conjugate to the fixed operator `fieldGenerator`. In characteristic two,
`N = u - 1` has fourth power zero and nonzero square. Stabilization of kernels
in dimension three gives `N³ = 0`. Choosing `v` with `N² v ≠ 0` produces the
basis `v, N v, N² v`: applying `N²` and then `N` to a linear relation proves
independence, and the dimension proves spanning. Matching this basis to the
corresponding basis for `fieldGenerator` constructs the conjugator on the
literal carrier, with the convention `d * u * d⁻¹ = fieldGenerator`.

This discharges precisely the first premise of
`EvenImage.exists_twist_of_pair_inputs`. The remaining normalized-pair
certificate and the final image-recognition assembly are separate.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453 (PDF p.464), for the three-dimensional F₄ setting. The argument
here supplies the order-four normalization used in the concrete recognition
of that action. The fixed operator comes from the licensed ATLAS hexacode
ports through `EvenImage.Operators`.
-/

public section

open Atlas.Codes Module
namespace Representation.Hexacode.SixDimensional.EvenImage

private theorem nilpotent_part (u : FieldGL) (h4 : u ^ 4 = 1) (h2 : u ^ 2 ≠ 1) :
    (u.toLinearMap - 1) ^ 3 = 0 ∧ (u.toLinearMap - 1) ^ 2 ≠ 0 := by
  have : Nontrivial hexacode := Module.nontrivial_of_finrank_pos
    (by rw [field_finrank]; decide : 0 < Module.finrank F hexacode)
  have : CharP (Module.End F hexacode) 2 := charP_of_injective_algebraMap' F 2
  let f := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := hexacode)
  have h4' : (u.toLinearMap - 1) ^ 4 = 0 := by
    have h := sub_pow_char_pow_of_commute (R := Module.End F hexacode) 2 2
      (Commute.one_right u.toLinearMap)
    change (u.toLinearMap - 1) ^ 4 = u.toLinearMap ^ 4 - 1 ^ 4 at h
    rw [h, one_pow]
    change f u ^ 4 - 1 = 0
    rw [← f.map_pow, h4, f.map_one, sub_self]
  constructor
  · have hker := Module.End.ker_pow_le_ker_pow_finrank (u.toLinearMap - 1) 4
    rw [field_finrank, h4', LinearMap.ker_zero] at hker
    exact LinearMap.ker_eq_top.mp (top_le_iff.mp hker)
  · intro hh
    apply h2
    apply LinearEquiv.toLinearMap_injective
    have h := sub_pow_char_of_commute (R := Module.End F hexacode) 2
      (Commute.one_right u.toLinearMap)
    rw [hh, one_pow] at h
    exact (f.map_pow u 2).trans ((sub_eq_zero.mp h.symm).trans f.map_one.symm)

private theorem chain_independent (N : Module.End F hexacode) (h3 : N ^ 3 = 0)
    (v : hexacode) (hv : N (N v) ≠ 0) :
    LinearIndependent F ![v, N v, N (N v)] := by
  have hv3 : N (N (N v)) = 0 := by
    simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, LinearMap.zero_apply]
      using LinearMap.congr_fun h3 v
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero] at hc
  change c 0 • v + (c 1 • N v + c 2 • N (N v)) = 0 at hc
  have hc1 := congrArg N hc
  simp only [map_add, map_smul, map_zero, hv3, smul_zero, add_zero] at hc1
  have hc2 := congrArg N hc1
  simp only [map_add, map_smul, map_zero, hv3, smul_zero, add_zero] at hc2
  have c0 : c 0 = 0 := (smul_eq_zero.mp hc2).resolve_right hv
  have c1 : c 1 = 0 := by
    rw [c0, zero_smul, zero_add] at hc1
    exact (smul_eq_zero.mp hc1).resolve_right hv
  have c2 : c 2 = 0 := by
    simp only [c0, c1, zero_smul, zero_add] at hc
    exact (smul_eq_zero.mp hc).resolve_right hv
  intro i
  fin_cases i <;> assumption

private theorem exists_chain_basis (N : Module.End F hexacode)
    (h3 : N ^ 3 = 0) (h2 : N ^ 2 ≠ 0) :
    ∃ b : Basis (Fin 3) F hexacode,
      N (b 0) = b 1 ∧ N (b 1) = b 2 ∧ N (b 2) = 0 := by
  have hn : ∃ v, N (N v) ≠ 0 := by
    by_contra! h
    apply h2
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hn
  let b := basisOfLinearIndependentOfCardEqFinrank (chain_independent N h3 v hv)
    (by simp [field_finrank])
  have hb : ∀ i, b i = ![v, N v, N (N v)] i := by
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hb, hb]
    rfl
  · rw [hb, hb]
    rfl
  · rw [hb]
    change N (N (N v)) = 0
    simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply,
      LinearMap.zero_apply] using LinearMap.congr_fun h3 v

private theorem exists_unipotent_basis (u : FieldGL) (h4 : u ^ 4 = 1) (h2 : u ^ 2 ≠ 1) :
    ∃ b : Basis (Fin 3) F hexacode,
      u (b 0) = b 1 + b 0 ∧ u (b 1) = b 2 + b 1 ∧ u (b 2) = b 2 := by
  obtain ⟨h3, hn2⟩ := nilpotent_part u h4 h2
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_chain_basis (u.toLinearMap - 1) h3 hn2
  change u (b 0) - b 0 = b 1 at hb0
  change u (b 1) - b 1 = b 2 at hb1
  change u (b 2) - b 2 = 0 at hb2
  exact ⟨b, sub_eq_iff_eq_add.mp hb0, sub_eq_iff_eq_add.mp hb1, sub_eq_zero.mp hb2⟩

/-- Every order-four operator on the actual F₄ hexacode is conjugate to the fixed
first generator. This is the order-four normalization input for even image recognition. -/
theorem exists_conjugator_of_order_four (u : FieldGL) (h4 : u ^ 4 = 1)
    (h2 : u ^ 2 ≠ 1) : ∃ d : FieldGL, MulAut.conj d u = fieldGenerator := by
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_unipotent_basis u h4 h2
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_unipotent_basis fieldGenerator
    fieldGenerator_four fieldGenerator_sq_ne_one
  let d : FieldGL := b.equiv c (_root_.Equiv.refl (Fin 3))
  have hd (i : Fin 3) : d (b i) = c i := b.equiv_apply i c (_root_.Equiv.refl (Fin 3))
  have hdu : d.toLinearMap.comp u.toLinearMap =
      fieldGenerator.toLinearMap.comp d.toLinearMap := by
    apply b.ext
    intro i
    change d (u (b i)) = fieldGenerator (d (b i))
    fin_cases i
    · change d (u (b 0)) = fieldGenerator (d (b 0))
      simp only [hb0, map_add, hd, hc0]
    · change d (u (b 1)) = fieldGenerator (d (b 1))
      simp only [hb1, map_add, hd, hc1]
    · change d (u (b 2)) = fieldGenerator (d (b 2))
      simp only [hb2, hd, hc2]
  refine ⟨d, ?_⟩
  apply LinearEquiv.ext
  intro w
  have hh := LinearMap.congr_fun hdu (d.symm w)
  change d (u (d.symm w)) = fieldGenerator (d (d.symm w)) at hh
  simpa only [MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    d.apply_symm_apply] using hh

end Representation.Hexacode.SixDimensional.EvenImage
