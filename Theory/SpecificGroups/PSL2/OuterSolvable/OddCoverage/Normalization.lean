module

public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.RootParameters
public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.RootGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Group

/-!
# Inner–diagonal normalization of odd PSL₂ automorphisms

Sylow conjugacy first arranges preservation of the upper root group. A lift
`A` of the image of the projective Weyl involution then has nonzero lower-left
entry, since that image is outside the root normalizer. The central square of
`A` forces its trace to vanish. Conjugating by the upper-triangular GL₂ matrix
`!![A₁₀,-A₀₀;0,1]` therefore sends `A` to the standard Weyl matrix. We realize
this conjugation as an upper-root inner automorphism times the prescribed
`diagonalAutHom` action, without constructing an automorphism lift.

The projective braid relation then forces the image of parameter one to be
one or minus one. The diagonal action at minus one fixes the projective Weyl
element and removes the second possibility. This proves the normalization
needed for the A₁ automorphism theorem in GLS3, Theorem 2.5.12 and §2.7,
including fields of cardinality nine and arbitrary finite-field carriers.
-/

namespace Theory.PSL2.OuterSolvable.OddCoverage
open Matrix
variable {K : Type*} [Field K]

private theorem weyl_mul_self : weyl K * weyl K = 1 := by
  change quotientMap K (slWeyl K) * quotientMap K (slWeyl K) = 1
  rw [← map_mul, ← map_one (quotientMap K)]
  apply (quotientMap_eq_iff _ _).mpr
  right
  apply Subtype.ext
  change (slWeyl K).val * (slWeyl K).val = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slWeyl, Matrix.mul_apply, Fin.sum_univ_two]

private theorem lowerLeft_image_weyl_ne_zero (hchar : ringChar K ≠ 2)
    (b : MulAut (Group K)) (hU : (rootGroup K).map b.toMonoidHom = rootGroup K)
    (A : SpecialLinearGroup (Fin 2) K) (hA : quotientMap K A = b (weyl K)) :
    A.val 1 0 ≠ 0 := by
  have hw : weyl K ∉ Subgroup.normalizer (rootGroup K : Set (Group K)) := by
    rw [weyl, quotient_mem_rootGroup_normalizer_iff hchar]
    exact one_ne_zero
  have hN : (Subgroup.normalizer (rootGroup K : Set (Group K))).map b.toMonoidHom =
      Subgroup.normalizer (rootGroup K : Set (Group K)) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  intro hc
  have hm : b (weyl K) ∈ Subgroup.normalizer (rootGroup K : Set (Group K)) := by
    rw [← hA, quotient_mem_rootGroup_normalizer_iff hchar]
    exact hc
  rw [← hN] at hm
  obtain ⟨g, hg, he⟩ := hm
  have heq : g = weyl K := b.injective he
  exact hw (heq ▸ hg)

private theorem trace_zero_of_projective_involution (A : SpecialLinearGroup (Fin 2) K)
    (hc : A.val 1 0 ≠ 0) (hA : quotientMap K A * quotientMap K A = 1) :
    A.val 1 1 = -A.val 0 0 := by
  have hcenter : A * A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change quotientMap K (A * A) = 1
    simpa only [map_mul] using hA
  have h10 : (A * A).val 1 0 = 0 := by
    rcases center_eq_one_or_neg_one _ hcenter with he | he <;> rw [he] <;> simp
  change (A.val * A.val) 1 0 = 0 at h10
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h10
  have hz : A.val 1 0 * (A.val 0 0 + A.val 1 1) = 0 := by
    linear_combination h10
  have hsum := (mul_eq_zero.mp hz).resolve_left hc
  linear_combination hsum

private theorem diagonal_preserves_root (u : Kˣ) :
    (rootGroup K).map (diagonalAutHom u).toMonoidHom = rootGroup K := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_rootGroup _).mp hy
    change diagonalAutHom u (upper t) ∈ rootGroup K
    rw [diagonalAut_upper]
    exact (mem_rootGroup _).mpr ⟨_, rfl⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := (mem_rootGroup _).mp hx
    refine ⟨upper ((↑u⁻¹ : K) * t), (mem_rootGroup _).mpr ⟨_, rfl⟩, ?_⟩
    change diagonalAutHom u (upper ((↑u⁻¹ : K) * t)) = upper t
    rw [diagonalAut_upper]
    simp

private theorem upper_conj_preserves_root (hchar : ringChar K ≠ 2) (t : K) :
    (rootGroup K).map (MulAut.conj (upper t)).toMonoidHom = rootGroup K := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
  rw [upper, quotient_mem_rootGroup_normalizer_iff hchar]
  rw [slUpper_val]
  rfl

private theorem normalize_weyl_matrix (A : SpecialLinearGroup (Fin 2) K)
    (hc : A.val 1 0 ≠ 0) (hd : A.val 1 1 = -A.val 0 0) :
    slUpper (-A.val 0 0) * slDiagonal (Units.mk0 (A.val 1 0) hc) A *
      (slUpper (-A.val 0 0))⁻¹ = slWeyl K := by
  have hdet : -(A.val 0 0 ^ 2) - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [det_fin_two, hd, mul_neg, ← pow_two] using A.property
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change (slUpper (-A.val 0 0)).val * (slDiagonal (Units.mk0 (A.val 1 0) hc) A).val =
    (slWeyl K).val * (slUpper (-A.val 0 0)).val
  rw [slUpper_val, slDiagonal_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slWeyl, Matrix.mul_apply, Fin.sum_univ_two, hd, hc]
  linear_combination -hdet


private theorem diagonal_mul_conj (u : Kˣ) (g : Group K) :
    diagonalAutHom u * MulAut.conj g =
      MulAut.conj (diagonalAutHom u g) * diagonalAutHom u := by
  ext x
  simp [MulAut.conj_apply]

private theorem exists_root_weyl_normalization [Finite K] (hchar : ringChar K ≠ 2)
    (a : MulAut (Group K)) :
    ∃ (g : Group K) (u : Kˣ) (b : MulAut (Group K)),
      a = MulAut.conj g * diagonalAutHom u * b ∧
      (rootGroup K).map b.toMonoidHom = rootGroup K ∧ b (weyl K) = weyl K := by
  obtain ⟨g, b, hab, hU⟩ := exists_root_normalization a
  obtain ⟨A, hA⟩ := quotientMap_surjective K (b (weyl K))
  have hc := lowerLeft_image_weyl_ne_zero hchar b hU A hA
  have hsq : quotientMap K A * quotientMap K A = 1 := by
    rw [hA, ← map_mul, weyl_mul_self, map_one]
  have hd := trace_zero_of_projective_involution A hc hsq
  let v := Units.mk0 (A.val 1 0) hc
  let q := upper (-A.val 0 0)
  let c := MulAut.conj q * diagonalAutHom v * b
  have hb : b = MulAut.conj (diagonalAutHom v⁻¹ q⁻¹) * diagonalAutHom v⁻¹ * c := by
    dsimp [c]
    rw [← diagonal_mul_conj]
    simp only [map_inv]
    group
  refine ⟨g * diagonalAutHom v⁻¹ q⁻¹, v⁻¹, c, ?_, ?_, ?_⟩
  · rw [hab, hb, map_mul]
    group
  · have hf : c.toMonoidHom = (MulAut.conj q).toMonoidHom.comp
        ((diagonalAutHom v).toMonoidHom.comp b.toMonoidHom) := by ext x; rfl
    rw [hf, ← Subgroup.map_map, ← Subgroup.map_map, hU, diagonal_preserves_root]
    exact upper_conj_preserves_root hchar _
  · change q * diagonalAutHom v (b (weyl K)) * q⁻¹ = weyl K
    rw [← hA, diagonalAutHom_apply_quotientMap]
    simpa only [map_mul, map_inv, q, v, upper, weyl] using
      congrArg (quotientMap K) (normalize_weyl_matrix A hc hd)

private theorem rootParameter_one_eq_one_or_neg_one (b : MulAut (Group K))
    (hU : (rootGroup K).map b.toMonoidHom = rootGroup K) (hw : b (weyl K) = weyl K) :
    rootParameter b hU 1 = 1 ∨ rootParameter b hU 1 = -1 := by
  have hbraid : upper (1 : K) * weyl K * upper 1 = weyl K * upper (-1) * weyl K := by
    change quotientMap K (slUpper 1) * quotientMap K (slWeyl K) * quotientMap K (slUpper 1) =
      quotientMap K (slWeyl K) * quotientMap K (slUpper (-1)) * quotientMap K (slWeyl K)
    simp only [← map_mul]
    apply (quotientMap_eq_iff _ _).mpr
    right
    apply Subtype.ext
    change (slUpper 1).val * (slWeyl K).val * (slUpper 1).val =
      -((slWeyl K).val * (slUpper (-1)).val * (slWeyl K).val)
    rw [slUpper_val, slUpper_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slWeyl, Matrix.mul_apply, Fin.sum_univ_two]
  have hn : rootParameter b hU (-1) = -rootParameter b hU 1 :=
    (rootParameterEquiv b hU).map_neg 1
  have he := congrArg b hbraid
  simp only [map_mul, map_upper b hU, hw, hn] at he
  change quotientMap K (slUpper (rootParameter b hU 1)) * quotientMap K (slWeyl K) *
      quotientMap K (slUpper (rootParameter b hU 1)) =
    quotientMap K (slWeyl K) * quotientMap K (slUpper (-rootParameter b hU 1)) *
      quotientMap K (slWeyl K) at he
  simp only [← map_mul] at he
  rcases (quotientMap_eq_iff _ _).mp he with hp | hm
  · right
    have he := congrArg Subtype.val hp
    change (slUpper (rootParameter b hU 1)).val * (slWeyl K).val *
        (slUpper (rootParameter b hU 1)).val =
      (slWeyl K).val * (slUpper (-rootParameter b hU 1)).val * (slWeyl K).val at he
    rw [slUpper_val, slUpper_val] at he
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) he
    simpa [slWeyl, Matrix.mul_apply, Fin.sum_univ_two] using h00
  · left
    have he := congrArg Subtype.val hm
    change (slUpper (rootParameter b hU 1)).val * (slWeyl K).val *
        (slUpper (rootParameter b hU 1)).val =
      -((slWeyl K).val * (slUpper (-rootParameter b hU 1)).val * (slWeyl K).val) at he
    rw [slUpper_val, slUpper_val] at he
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) he
    simpa [slWeyl, Matrix.mul_apply, Fin.sum_univ_two] using h00

private theorem diagonal_neg_one_weyl : diagonalAutHom (-1 : Kˣ) (weyl K) = weyl K := by
  rw [weyl, diagonalAutHom_apply_quotientMap]
  apply (quotientMap_eq_iff _ _).mpr
  right
  apply Subtype.ext
  change (slDiagonal (-1 : Kˣ) (slWeyl K)).val = -(slWeyl K).val
  rw [slDiagonal_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slWeyl]

public theorem exists_root_weyl_one_normalization [Finite K] (hchar : ringChar K ≠ 2)
    (a : MulAut (Group K)) :
    ∃ (g : Group K) (u : Kˣ) (b : MulAut (Group K)),
      a = MulAut.conj g * diagonalAutHom u * b ∧
      (rootGroup K).map b.toMonoidHom = rootGroup K ∧
      b (weyl K) = weyl K ∧ b (upper 1) = upper 1 := by
  obtain ⟨g, u, b, hab, hU, hw⟩ := exists_root_weyl_normalization hchar a
  rcases rootParameter_one_eq_one_or_neg_one b hU hw with h1 | h1
  · refine ⟨g, u, b, hab, hU, hw, ?_⟩
    rw [map_upper b hU, h1]
  · refine ⟨g, u * (-1), diagonalAutHom (-1) * b, ?_, ?_, ?_, ?_⟩
    · rw [map_mul]
      have hh : diagonalAutHom (-1 : Kˣ) * diagonalAutHom (-1) = 1 := by
        rw [← map_mul]
        simp
      simpa only [mul_assoc, ← mul_assoc (diagonalAutHom (-1 : Kˣ)), hh, one_mul] using hab
    · have hf : (diagonalAutHom (-1 : Kˣ) * b).toMonoidHom =
          (diagonalAutHom (-1 : Kˣ)).toMonoidHom.comp b.toMonoidHom := by ext x; rfl
      rw [hf, ← Subgroup.map_map, hU, diagonal_preserves_root]
    · change diagonalAutHom (-1 : Kˣ) (b (weyl K)) = weyl K
      rw [hw, diagonal_neg_one_weyl]
    · change diagonalAutHom (-1 : Kˣ) (b (upper 1)) = upper 1
      rw [map_upper b hU, h1, diagonalAut_upper]
      simp

end Theory.PSL2.OuterSolvable.OddCoverage
