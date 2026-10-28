module

public import Theory.SpecificGroups.SU3.OddInvolutionNormalization
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ReduceModChar

/-!
# Seven-elements inverted by outer involutions of PSU₃(5)

Over a field of order 25, choose `t` with `t² = 2`; its fifth power is `-t`.
An explicit matrix `M t` preserves the antidiagonal Hermitian form, has
determinant one, and has inverse `M (-t)`. Four small matrix-product
identities certify its seventh power. Its entry in position `(0, 1)` is one,
so it is not scalar and its projective image has order seven.

Every outer involution is transported to entrywise conjugation by the actual
equivalence from `OddInvolutionNormalization.normalized_outer`. Transporting
the matrix witness back proves the assertion for an arbitrary nondegenerate
Hermitian form. Simplicity is used only for that normalization; no module,
generation, or displacement premise is required.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11; Aschbacher–Smith K.2, printed p.453. The explicit matrix
and its product calculations give the inverted seven-element asserted there.
-/

open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.FiveOuterSeven

section CharacteristicFive
variable {F : Type*} [Field F] [CharP F 5]
private def M (t : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 1, 2 - 2 * t; -1 - t, -t, 1; -2, -1 - t, 1]
private def Q (t : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1 - 2 * t, -2 - t, t; -1, -2 * t, -2 - t; -1 + 2 * t, -1, 1 - 2 * t]
private def C (t : F) : Matrix (Fin 3) (Fin 3) F :=
  !![-t, 1 - t, -2 - t; 2 - t, 2 - 2 * t, 1 - t; -2 + 2 * t, 2 - t, -t]
private theorem matrix_mul_conjugate {t : F} (ht : t ^ 2 = 2) : M t * M (-t) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> (try simp only [ht]) <;> (try ring_nf) <;> reduce_mod_char!
private theorem matrix_det {t : F} (ht : t ^ 2 = 2) : (M t).det = 1 := by
  simp [M, Matrix.det_fin_three]
  ring_nf
  have ht3 : t ^ 3 = 2 * t := by rw [pow_succ, ht]
  simp only [ht, ht3]
  ring_nf
  reduce_mod_char!
private theorem matrix_square {t : F} (ht : t ^ 2 = 2) : M t ^ 2 = Q t := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Q, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> (try simp only [ht]) <;> (try ring_nf) <;>
      reduce_mod_char! <;> (try ring_nf) <;> reduce_mod_char!
private theorem matrix_cube_step {t : F} (ht : t ^ 2 = 2) : Q t * M t = C t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Q, C, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> (try simp only [ht]) <;> (try ring_nf) <;>
      reduce_mod_char! <;> (try ring_nf); reduce_mod_char!
private theorem matrix_fourth_step {t : F} (ht : t ^ 2 = 2) : C t * M t = C (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, C, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> (try simp only [ht]) <;> (try ring_nf) <;>
      reduce_mod_char! <;> (try ring_nf) <;> reduce_mod_char!
private theorem cube_mul_conjugate {t : F} (ht : t ^ 2 = 2) : C t * C (-t) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> (try simp only [ht]) <;> (try ring_nf) <;> reduce_mod_char!
omit [CharP F 5] in
private theorem matrix_conjugate (J : HermitianForm 3 F) {t : F} (hc : J.conj t = -t) :
    (M t).map J.conj = M (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, hc, map_ofNat]
omit [CharP F 5] in
private theorem matrix_selfadjoint (t : F) :
    (M t).transpose * !![0, 0, 1; 0, 1, 0; 1, 0, 0] =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] * M t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_apply, Fin.sum_univ_three]

private theorem matrix_pow_seven {t : F} (ht : t ^ 2 = 2) : M t ^ 7 = 1 := by
  have h3 : M t ^ 3 = C t := by
    rw [pow_succ (n := 2), matrix_square ht]
    exact matrix_cube_step ht
  have h4 : M t ^ 4 = C (-t) := by
    rw [pow_succ (n := 3), h3]
    exact matrix_fourth_step ht
  rw [show (7 : ℕ) = 3 + 4 from rfl, pow_add, h3, h4]
  exact cube_mul_conjugate ht

private theorem exists_square_root_two [Finite F] (hcard : Nat.card F = 25) : ∃ t : F, t ^ 2 = 2 := by
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 25 := by simpa only [Nat.card_eq_fintype_card] using hcard
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F 5]; decide
  have h2 : (2 : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two (by decide)
  have hs : IsSquare (2 : F) := (FiniteField.isSquare_iff hchar h2).mpr (by
    rw [hc]; norm_num; reduce_mod_char!)
  obtain ⟨t, ht⟩ := hs
  exact ⟨t, by simpa only [pow_two] using ht.symm⟩

private def matrixUnit {t : F} (ht : t ^ 2 = 2) : GL (Fin 3) F where
  val := M t
  inv := M (-t)
  val_inv := matrix_mul_conjugate ht
  inv_val := by simpa using matrix_mul_conjugate (t := -t) (by simpa using ht)

private theorem matrix_unitary (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {t : F} (ht : t ^ 2 = 2) (hc : J.conj t = -t) :
    J.conjTranspose (M t) * J.form * M t = J.form := by
  have hmap : J.conjTranspose (M t) = (M (-t)).transpose := by
    change ((M t).map J.conj).transpose = _
    rw [matrix_conjugate J hc]
  rw [hmap, hJ, matrix_selfadjoint, mul_assoc,
    show M (-t) * M t = 1 from by
      simpa using matrix_mul_conjugate (t := -t) (by simpa using ht), mul_one]

private theorem projective_witness (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {t : F} (ht : t ^ 2 = 2) (hc : J.conj t = -t)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : J.IsEntrywiseConjugation a) :
    ∃ s, orderOf s = 7 ∧ a s = s⁻¹ := by
  let x : J.specialSubgroup := ⟨matrixUnit ht, by
    rw [J.mem_specialSubgroup_iff]
    refine ⟨matrix_unitary J hJ ht hc, ?_⟩
    apply Units.ext
    exact matrix_det ht⟩
  have hxpow : x ^ 7 = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact matrix_pow_seven ht
  let s := J.specialToProjective x
  have hs : s ≠ 1 := by
    intro hs
    have hscalar : x.val ∈ Subgroup.center (GL (Fin 3) F) := by
      apply ProjGenLinGroup.mk_eq_one.mp
      have hv := congrArg Subtype.val hs
      change (J.specialToProjective x).val = (1 : ProjectiveSpecialUnitaryMatrixGroup J).val at hv
      simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using hv
    rw [GeneralLinearGroup.center_eq_range_scalar] at hscalar
    obtain ⟨u, hu⟩ := hscalar
    have hentry := congrArg (fun g : GL (Fin 3) F => g.val 0 1) hu
    simp [x, matrixUnit, M, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hentry
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine ⟨s, orderOf_eq_prime (by
    change (J.specialToProjective x) ^ 7 = 1
    rw [← map_pow, hxpow, map_one]) hs, ?_⟩
  obtain ⟨y, hy, hay⟩ := ha x
  have hyx : y = x⁻¹ := by
    apply Subtype.ext
    apply Units.ext
    change y.val.val = M (-t)
    rw [hy]
    exact matrix_conjugate J hc
  change a (J.specialToProjective x) = _
  rw [hay, hyx, map_inv]

/-- Entrywise Hermitian conjugation inverts an element of order seven in the
actual projective special unitary group of the antidiagonal form. -/
public theorem entrywise_inverts_seven [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card F = 5 ^ 2) (hc : ∀ x, J.conj x = x ^ 5)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : J.IsEntrywiseConjugation a) :
    ∃ s, orderOf s = 7 ∧ a s = s⁻¹ := by
  obtain ⟨t, ht⟩ := exists_square_root_two hcard
  apply projective_witness J hJ ht (t := t) (a := a) ?_ ha
  rw [hc]
  calc
    t ^ 5 = (t ^ 2) ^ 2 * t := by ring
    _ = -t := by rw [ht]; ring_nf; reduce_mod_char!; ring

end CharacteristicFive

/-- Every outer involution of the genuine PSU₃(5) model inverts an element
of order seven, independently of the nondegenerate Hermitian Gram matrix. -/
public theorem exists_inverted_seven_of_outer_involution
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hcard : Nat.card F = 5 ^ 2) (hc : ∀ x, J.conj x = x ^ 5)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ s, a = MulAut.conj s) :
    ∃ s, orderOf s = 7 ∧ a s = s⁻¹ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow (f := 2) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hfixed : Nat.card {x : F // J.conj x = x} = 5 := by
    exact FiniteField.card_fixed_of_quadratic_frobenius J.conj 5 1 (by decide)
      hcard hc
  obtain ⟨J₀, e, hconj, hform, hentry⟩ :=
    OddInvolutionNormalization.normalized_outer J (by decide : Nat.Prime 5)
      (by decide : Odd 5) hcard hfixed a ha houter
  have hc₀ : ∀ x, J₀.conj x = x ^ 5 := by rw [hconj]; exact hc
  obtain ⟨s, hs, has⟩ := entrywise_inverts_seven J₀ hform hcard hc₀
    (MulAut.congr e a) hentry
  refine ⟨e.symm s, (e.symm.orderOf_eq s).trans hs, ?_⟩
  apply e.injective
  change e (a (e.symm s)) = s⁻¹ at has
  simpa only [map_inv, MulEquiv.apply_symm_apply] using has

end BenderSuzuki.MatrixGroups.HermitianForm.FiveOuterSeven
