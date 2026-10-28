module

public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Prime-to-p residuals of SL₂ and GL₂

Every transvection in characteristic p is killed by p. Transvection induction
therefore puts every homomorphic image of SL₂ into the prime-to-p residual
of its target. In GL₂ over the prime field, the determinant kernel is exactly
this residual: the opposite inclusion follows because the determinant image
has order dividing p - 1. In particular the result includes p = 3 and uses
no perfectness assumption.

Source: the elementary matrix calculation used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.3.21(a), printed p. 55.
-/

public section

open Matrix
namespace Matrix.SL2
variable {F G : Type*} [Field F] [Group G] (p : ℕ) [CharP F p]

private theorem transvection_pow_char {i j : Fin 2} (hij : i ≠ j) (c : F) :
    SpecialLinearGroup.transvection hij c ^ p = 1 := by
  have hpow (n : ℕ) : SpecialLinearGroup.transvection hij c ^ n =
      SpecialLinearGroup.transvection hij (n • c) := by
    induction n with
    | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
    | succ n ih =>
      rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]
  simpa [nsmul_eq_mul, CharP.cast_eq_zero F p,
    SpecialLinearGroup.transvection_coeff_zero] using hpow p

/-- Every image of SL₂ in characteristic p lies in the prime-to-p residual. -/
theorem map_mem_primeToResidual (f : SpecialLinearGroup (Fin 2) F →* G)
    (A : SpecialLinearGroup (Fin 2) F) : f A ∈ Subgroup.primeToResidual p G := by
  apply transvection_induction (fun A => f A ∈ Subgroup.primeToResidual p G) ?_ ?_ A
  · intro i j hij c
    apply Subgroup.mem_primeToResidual_of_pow (n := 1)
    simpa using congrArg f (transvection_pow_char p hij c)
  · intro A B hA hB
    simpa using (Subgroup.primeToResidual p G).mul_mem hA hB

end Matrix.SL2

namespace Matrix.GeneralLinearGroup

/-- O^{p′}(GL₂(p)) is exactly its determinant kernel, also for p = 3. -/
theorem primeToResidual_eq_det_ker (p : ℕ) [Fact p.Prime] :
    Subgroup.primeToResidual p (GL (Fin 2) (ZMod p)) =
      (det (n := Fin 2) (R := ZMod p)).ker := by
  apply le_antisymm
  · apply Subgroup.primeToResidual_le_ker
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
    exact (Nat.coprime_self_sub_right (Fact.out : p.Prime).one_lt.le).mpr
      (Nat.coprime_one_right p)
  · intro A hA
    let S : SpecialLinearGroup (Fin 2) (ZMod p) :=
      ⟨(A : Matrix (Fin 2) (Fin 2) (ZMod p)), Units.ext_iff.mp hA⟩
    have hS : SpecialLinearGroup.toGL S = A := by
      apply GeneralLinearGroup.ext
      intro i j
      rfl
    rw [← hS]
    exact Matrix.SL2.map_mem_primeToResidual p SpecialLinearGroup.toGL S

end Matrix.GeneralLinearGroup

end
