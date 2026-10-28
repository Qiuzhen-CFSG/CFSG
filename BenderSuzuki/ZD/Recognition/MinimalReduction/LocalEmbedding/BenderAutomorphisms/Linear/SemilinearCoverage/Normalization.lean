module
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage.RootParameters
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Inner normalization of automorphisms of binary SL₂

Sylow conjugacy first arranges preservation of the upper root group. The image
of the Weyl involution then has nonzero lower-left entry: otherwise it would lie
in that root group. If its entries are `!![a, b; c, a]`, choose `r² = c` and use
`!![r, a/r; 0, r⁻¹]` to conjugate it to the standard Weyl matrix. This matrix is
in the Borel and hence preserves the upper root group. The argument includes
SL₂(2) and SL₂(4), without simplicity or an automorphism-classification input.

This is the normalization step for GLS, Volume 4, Chapter 4, Lemma 3.1(a),
and the automorphism classification used in Lemma 3.4(c).
-/

namespace BenderSuzuki.ZD.Linear
open Converse
open scoped Pointwise
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
private theorem Unip_eq_upperUnipotent : Unip K = Matrix.SpecialLinearGroup.upperUnipotent K := by
  ext g
  rw [mem_Unip_iff, Matrix.SpecialLinearGroup.mem_upperUnipotent]
  simp only [upper_transvection_eq_uni, eq_comm]

private theorem exists_preserves_root [Finite K] (a : MulAut (SL2 K)) :
    ∃ (g : SL2 K) (b : MulAut (SL2 K)),
      a = MulAut.conj g * b ∧ (Unip K).map b.toMonoidHom = Unip K := by
  let P := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 K) (a • P) P
  have he := congrArg (fun Q : Sylow 2 (SL2 K) => (Q : Subgroup (SL2 K))) hg
  have hm : (Unip K).map (MulAut.conj g * a).toMonoidHom = Unip K := by
    change ((Matrix.SpecialLinearGroup.upperUnipotent K).map a.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = Matrix.SpecialLinearGroup.upperUnipotent K at he
    rw [← Unip_eq_upperUnipotent] at he
    rw [Subgroup.map_map] at he
    have hf : (MulAut.conj g * a).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp a.toMonoidHom := by ext x; rfl
    rw [hf]
    exact he
  refine ⟨g⁻¹, MulAut.conj g * a, ?_, hm⟩
  rw [map_inv, inv_mul_cancel_left]

omit [CharP K 2] in
private theorem conj_Borel_preserves_root (g : SL2 K) (hg : g ∈ Borel K) :
    (Unip K).map (MulAut.conj g).toMonoidHom = Unip K := by
  apply le_antisymm
  · rintro x ⟨u, hu, rfl⟩
    exact Unip_conj_mem hg hu
  · intro u hu
    refine ⟨g⁻¹ * u * g, ?_, ?_⟩
    · change g⁻¹ * u * g ∈ Unip K
      simpa only [inv_inv] using Unip_conj_mem ((Borel K).inv_mem hg) hu
    · simp [MulAut.conj_apply, mul_assoc]

private theorem lower_left_ne_zero_of_root_weyl (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) : (a (weyl K)).val 1 0 ≠ 0 := by
  intro hc
  let A := a (weyl K)
  have hsq : A * A = 1 := by dsimp [A]; rw [← map_mul, weyl_sq, map_one]
  have h00sq := congrArg (fun g : SL2 K => g.val 0 0) hsq
  have h00 : A.val 0 0 = 1 := by
    apply CharTwo.sq_injective
    simpa [Matrix.mul_apply, Fin.sum_univ_two, A, hc, pow_two] using h00sq
  have h11 : A.val 1 1 = 1 := by
    have hdet := A.property
    simpa only [Matrix.det_fin_two, h00, show A.val 1 0 = 0 from hc,
      one_mul, mul_zero, sub_zero] using hdet
  have hm : A ∈ Unip K := by
    apply (mem_Unip_iff _).mpr
    refine ⟨A.val 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, show A.val 1 0 = 0 from hc]
  rw [← hU] at hm
  obtain ⟨g, hg, he⟩ := hm
  have he' : g = weyl K := a.injective he
  have hw := Unip_le_Borel hg
  rw [he'] at hw
  exact weyl_notMem_Borel hw

private theorem exists_Borel_conj_weyl [Finite K] (A : SL2 K)
    (hAA : A * A = 1) (hc : A.val 1 0 ≠ 0) :
    ∃ h : SL2 K, h ∈ Borel K ∧ h * A * h⁻¹ = weyl K := by
  have hd : A.val 1 1 = A.val 0 0 := by
    have he := congrArg (fun g : SL2 K => g.val 1 0) hAA
    have he0 : A.val 1 0 * A.val 0 0 + A.val 1 1 * A.val 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using he
    have he' : (A.val 1 1 + A.val 0 0) * A.val 1 0 = 0 := by
      linear_combination he0
    exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hc)
  have hdet : A.val 0 0 * A.val 0 0 + A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hd, CharTwo.sub_eq_add] using A.property
  obtain ⟨r, hr2⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := K))) (A.val 1 0)
  change r ^ 2 = A.val 1 0 at hr2
  have hr : r ≠ 0 := by intro hz; apply hc; rw [← hr2, hz]; simp
  let h : SL2 K := ⟨!![r, A.val 0 0 / r; 0, r⁻¹], by
    simp [Matrix.det_fin_two, hr]⟩
  have hcr : r⁻¹ * A.val 1 0 = r := by
    rw [← hr2, pow_two, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
  have hrel : h * A = weyl K * h := by
    apply Subtype.ext
    change h.val * A.val = (weyl K).val * h.val
    ext i j
    fin_cases i <;> fin_cases j
    · simp [h, Matrix.mul_apply, Fin.sum_univ_two]
      rw [div_eq_mul_inv, mul_assoc, hcr, mul_comm r, CharTwo.add_self_eq_zero]
    · simp [h, Matrix.mul_apply, Fin.sum_univ_two, hd]
      field_simp
      linear_combination hdet + A.val 0 1 * hr2
    · simpa [h, Matrix.mul_apply, Fin.sum_univ_two] using hcr
    · simp [h, Matrix.mul_apply, Fin.sum_univ_two, hd, div_eq_mul_inv, mul_comm]
  refine ⟨h, ?_, ?_⟩
  · rw [mem_Borel_iff]; simp [h]
  · rw [hrel, mul_inv_cancel_right]

/-- Inner normalization of an arbitrary automorphism, including the field of two elements. -/
public theorem exists_root_weyl_normalization [Finite K] (a : MulAut (SL2 K)) :
    ∃ (g : SL2 K) (b : MulAut (SL2 K)),
      a = MulAut.conj g * b ∧ (Unip K).map b.toMonoidHom = Unip K ∧
        b (weyl K) = weyl K := by
  obtain ⟨g, b, hab, hU⟩ := exists_preserves_root a
  have hbb : b (weyl K) * b (weyl K) = 1 := by rw [← map_mul, weyl_sq, map_one]
  obtain ⟨h, hB, hw⟩ := exists_Borel_conj_weyl (b (weyl K)) hbb
    (lower_left_ne_zero_of_root_weyl b hU)
  refine ⟨g * h⁻¹, MulAut.conj h * b, ?_, ?_, ?_⟩
  · simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using hab
  · have hf : (MulAut.conj h * b).toMonoidHom =
        (MulAut.conj h).toMonoidHom.comp b.toMonoidHom := by ext x; rfl
    rw [hf, ← Subgroup.map_map, hU]
    exact conj_Borel_preserves_root h hB
  · exact hw

end BenderSuzuki.ZD.Linear
