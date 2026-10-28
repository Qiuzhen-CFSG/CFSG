module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.LinearCocycle
import all Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.LinearCocycle

/-!
# Ternary linear descent for every odd prime

A matrix cocycle descends using a norm-one parameter outside the roots of a
cubic characteristic polynomial. The norm-one group has p + 1 > 3 elements,
including when p = 3. Scalar Hilbert 90 then constructs the descent basis.

This extends the proof in
`OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.LinearCocycle`
from p ≡ 3 modulo eight to every odd prime, leaving that interface intact.
The internal import reuses its private parameter lemmas as a deliberate
proof split, preserving the existing public boundary. Source: GLS3, §§2.7 and 4.3; the involution inspection in
Aschbacher–Smith E.6.18, printed p.252, and Theorem C, printed p.33.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

open OddPrimeSylow.NormalizedOuter.Descent

/-- Every ternary cocycle for quadratic finite-field conjugation has a linear
descent basis. The odd-prime hypotheses include characteristic three. -/
public theorem linear_cocycle_descent [Finite E]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (A : GL (Fin 3) E)
    (hA : A * GeneralLinearGroup.map J.conj.toRingHom A = 1) :
    ∃ P : GL (Fin 3) E, A * GeneralLinearGroup.map J.conj.toRingHom P = P := by
  classical
  have hne : ∃ s : E, J.conj s ≠ s := by
    by_contra h
    push Not at h
    let e : {x : E // J.conj x = x} ≃ E :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, h x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Nat.card_congr e
    rw [hfixed, hcard] at hc
    have := hp.two_le
    nlinarith
  obtain ⟨k, hkdet⟩ := exists_norm_parameter hcard (by have := hp.two_le; obtain ⟨k, hk⟩ := ho; omega : 2 < p) A.val
  have hkpow : (k.val : E) ^ (p + 1) = 1 :=
    (mem_rootsOfUnity' (p + 1) k.val).mp k.property
  have hknorm : J.conj (k.val : E) * (k.val : E) = 1 := by
    rw [BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J p hcard hfixed]
    simpa only [pow_succ] using hkpow
  obtain ⟨t, ht0, ht⟩ := scalar_descent_parameter J hne (k.val : E) hknorm
  let B : Matrix (Fin 3) (Fin 3) E := t • 1 + J.conj t • A.val
  have hBfactor : B = J.conj t • (Matrix.scalar (Fin 3) (k.val : E) + A.val) := by
    rw [smul_add]
    ext i j
    by_cases hij : i = j <;> simp [B, Matrix.scalar_apply, hij, ht]
  have hBdet : B.det ≠ 0 := by
    rw [hBfactor, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by simpa using ht0)) hkdet
  have hAm : A.val * A.val.map J.conj = 1 := congrArg Units.val hA
  have hBmap : B.map J.conj = J.conj t • 1 + t • A.val.map J.conj := by
    ext i j
    simp only [B, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, J.conj_involutive t]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hB : A.val * B.map J.conj = B := by
    rw [hBmap, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hAm, Matrix.mul_one]
    exact add_comm _ _
  refine ⟨GeneralLinearGroup.mkOfDetNeZero B hBdet, ?_⟩
  apply Units.ext
  exact hB

end BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
