module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear
public import BenderSuzuki.External.Huppert.II.theorem_10_12
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Faithfulness of the semilinear field component on PSU₃

A unitary-semilinear formula for the identity on the actual projective SU₃
image has trivial field part. Trace one removes the projective scalar from
each root-matrix equation. The upper and lower central roots then force the
three off-diagonal entries needed to compare the first coordinate of every
upper root. These comparisons give `c * σ(a) = a * d` for every field element
`a`, with `c ≠ 0`; taking `a = 1` finishes the separation argument.

Every first root coordinate is realized: a nontrivial Hermitian involution
has a trace-one element `t / (t + conj(t))`, which can be multiplied by the
norm of the desired coordinate. The cardinality hypotheses provide
characteristic two and nontriviality of the involution.

This is the field/inner-diagonal separation in GLS, Volume 3,
Theorem 2.5.12(a,d,f), under Section 2.7's matrix identifications
`Inndiag(PSU₃(q)) = PGU₃(q)` and `Φ = Aut(GF(q²))`.
The proof uses the actual Huppert II.10.12 root matrices and does not require
coverage of arbitrary automorphisms by semilinear formulas.
-/

open BenderSuzuki.MatrixGroups Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E]

private theorem semilinear_of_trace_one (A X : GL (Fin 3) E) (σ : E ≃+* E)
    (hX : X.val.trace = 1)
    (h : ProjGenLinGroup.mk X = ProjGenLinGroup.mk A *
      ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.mk X) *
      (ProjGenLinGroup.mk A)⁻¹) :
    A.val * X.val.map σ = X.val * A.val := by
  have hp : ProjGenLinGroup.mk (A * GeneralLinearGroup.map σ.toRingHom X * A⁻¹) =
      ProjGenLinGroup.mk X := by
    simpa only [map_mul, map_inv, ProjGenLinGroup.map_mk] using h.symm
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have ht := congrArg (fun B : GL (Fin 3) E => B.val.trace) hc
  have hm : ((A * GeneralLinearGroup.map σ.toRingHom X * A⁻¹) *
      GeneralLinearGroup.scalar (Fin 3) c).val =
      (c : E) • (A.val * X.val.map σ * (A⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  rw [hm, trace_smul, trace_units_conj, ← AddMonoidHom.map_trace, hX, map_one,
    smul_eq_mul, mul_one] at ht
  have hc1 : c = 1 := Units.ext ht
  rw [hc1, map_one, mul_one] at hc
  exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp hc)

section Binary
variable (J : HermitianForm 3 E) [CharP E 2]
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private def upperRoot : J.specialSubgroup :=
  hermitianUnipotentSU J hJ ⟨(0, 1), by simp [CharTwo.add_self_eq_zero]⟩

private def lowerRoot : J.specialSubgroup := by
  let L : Matrix (Fin 3) (Fin 3) E := !![1, 0, 0; 0, 1, 0; 1, 0, 1]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero L (by simp [L, det_fin_three]), ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        CharTwo.add_self_eq_zero]
  · apply Units.ext
    change L.det = 1
    simp [L, det_fin_three]

private theorem exists_trace_one (hconj : J.conj ≠ 1) :
    ∃ b : E, b + J.conj b = 1 := by
  have hex : ∃ t : E, J.conj t ≠ t := by
    by_contra! h
    exact hconj (RingEquiv.ext h)
  obtain ⟨t, ht⟩ := hex
  have hden : t + J.conj t ≠ 0 := by
    intro h
    apply ht
    calc
      J.conj t = t + (t + J.conj t) := by simp [← add_assoc, CharTwo.add_self_eq_zero]
      _ = t := by rw [h, add_zero]
  refine ⟨t / (t + J.conj t), ?_⟩
  rw [map_div₀, map_add, J.conj_involutive, add_comm (J.conj t) t,
    ← add_div, div_self hden]

private theorem exists_root_coord (hconj : J.conj ≠ 1) (a : E) :
    ∃ z : hermitianUnipotentCoord J, z.val.1 = a := by
  obtain ⟨b, hb⟩ := exists_trace_one J hconj
  refine ⟨⟨(a, (a * J.conj a) * b), ?_⟩, rfl⟩
  dsimp only
  rw [map_mul, map_mul, J.conj_involutive]
  calc
    a * J.conj a * b + J.conj a * a * J.conj b + a * J.conj a =
      a * J.conj a * (b + J.conj b + 1) := by ring
    _ = 0 := by rw [hb, CharTwo.add_self_eq_zero, mul_zero]

include hJ in
private theorem field_eq_one_of_nontrivial_conj
    (hconj : J.conj ≠ 1) (σ : E ≃+* E)
    (hσ : J.HasUnitarySemilinearForm 1 σ) : σ = 1 := by
  obtain ⟨u, hu⟩ := hσ
  let A := u.val
  have hsem (X : J.specialSubgroup) (htr : X.val.val.trace = 1) :
      A.val * X.val.val.map σ = X.val.val * A.val := by
    apply semilinear_of_trace_one A X.val σ htr
    simpa only [MulAut.one_apply, specialToProjective_apply_val] using
      hu (J.specialToProjective X)
  have hUmat : (upperRoot J hJ).val.val = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
    simp [upperRoot, hermitianUnipotentSU, hermitianUnipotentGL, hermitianUnipotentMatrix]
  have hUfixed : (upperRoot J hJ).val.val.map σ = (upperRoot J hJ).val.val := by
    rw [hUmat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hLfixed : (lowerRoot J hJ).val.val.map σ = (lowerRoot J hJ).val.val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerRoot]
  have hU := hsem (upperRoot J hJ) (by
    rw [hUmat]
    simp [Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  have hL := hsem (lowerRoot J hJ) (by
    simp [lowerRoot, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  rw [hUfixed, hUmat] at hU
  rw [hLfixed] at hL
  change A.val * !![1, 0, 0; 0, 1, 0; 1, 0, 1] =
    !![1, 0, 0; 0, 1, 0; 1, 0, 1] * A.val at hL
  have h21 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hU
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hL
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 1) hL
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h21 h02 h01
  have hroot (z : hermitianUnipotentCoord J) :
      A.val 0 0 * σ z.val.1 = z.val.1 * A.val 1 1 := by
    have hz := hsem (hermitianUnipotentSU J hJ z) (by
      simp [hermitianUnipotentSU, hermitianUnipotentGL, hermitianUnipotentMatrix,
        Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hz
    simpa [hermitianUnipotentSU, hermitianUnipotentGL, hermitianUnipotentMatrix,
      Matrix.mul_apply, Fin.sum_univ_three, h01, h21] using he
  obtain ⟨z, hz⟩ := exists_root_coord J hconj 1
  have hmid : A.val 0 0 = A.val 1 1 := by simpa [hz] using hroot z
  have h00 : A.val 0 0 ≠ 0 := by
    intro hzero
    have hinv : A.val * (A⁻¹).val = 1 := by simp
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 0) hinv
    simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, hzero] at he
  apply RingEquiv.ext
  intro a
  obtain ⟨z, rfl⟩ := exists_root_coord J hconj a
  change σ z.val.1 = z.val.1
  apply mul_left_cancel₀ h00
  rw [hroot, ← hmid, mul_comm]

end Binary

variable (J : HermitianForm 3 E)

/-- A concrete unitary-semilinear formula for the identity automorphism of
PSU₃ has trivial field part. This discharges the field-faithfulness premise
in the outer-involution normal-form and PSU₃(8) centralizer reductions. -/
public theorem semilinear_identity_field_eq_one [Finite E] (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (σ : E ≃+* E) (hσ : J.HasUnitarySemilinearForm 1 σ) : σ = 1 := by
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact field_eq_one_of_nontrivial_conj J hJ (conj_ne_one_of_card J n hn hcard hfixed) σ hσ

end BenderSuzuki.MatrixGroups.HermitianForm
