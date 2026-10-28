module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation
import BenderSuzuki.External.Huppert.II.theorem_10_4
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Ternary linear descent over an odd quadratic finite field

For a matrix cocycle `A * conj(A) = 1`, the matrix
`B = t • 1 + conj(t) • A` satisfies `A * conj(B) = B`.
The norm-one group has `p + 1 > 3` elements, so one of its elements `k`
is not a root of the degree-three characteristic polynomial of `-A`.
Scalar Hilbert 90 supplies nonzero `t` with `conj(t) * k = t`, making
`B = conj(t) • (k • 1 + A)` invertible. The parameter `k = -1` uses a
nonzero difference `s - conj(s)`, so it is included in the root count.

This proves exactly the linear input of
`Descent.projective_descent_of_linear_and_similarity`, including `p = 3`.
No condition on the Gram matrix is needed. The norm-one cardinality argument
follows `exists_hermitian_norm_one_torus_cube_ne_one` in Huppert II.10.12;
Huppert II.10.4 identifies the stored conjugation with the `p`-power map.

Source: GLS3, §§2.7 and 4.3; Aschbacher–Smith F.6.18(10)–(11),
printed pp.309–310 (PDF pp.320–321). This is the linear descent ingredient,
with projective and unitary assembly left to the parent module.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The elementary scalar Hilbert–90 parameterization includes `-1`. -/
private theorem scalar_descent_parameter
    (hne : ∃ s : E, J.conj s ≠ s) (k : E)
    (hk : J.conj k * k = 1) :
    ∃ t : E, t ≠ 0 ∧ J.conj t * k = t := by
  by_cases hkneg : k = -1
  · obtain ⟨s, hs⟩ := hne
    refine ⟨s - J.conj s, sub_ne_zero.mpr (Ne.symm hs), ?_⟩
    rw [hkneg, map_sub, J.conj_involutive]
    ring
  · refine ⟨1 + k, ?_, ?_⟩
    · intro h
      apply hkneg
      linear_combination h
    · rw [map_add, map_one, add_mul, one_mul, hk, add_comm]

/-- A cubic cannot vanish on all `p + 1` norm-one parameters. -/
private theorem exists_norm_parameter [Finite E]
    {p : ℕ} (hcard : Nat.card E = p ^ 2) (hp : 2 < p)
    (A : Matrix (Fin 3) (Fin 3) E) :
    ∃ k : rootsOfUnity (p + 1) E,
      (Matrix.scalar (Fin 3) (k.val : E) + A).det ≠ 0 := by
  classical
  have hcardUnits : Nat.card Eˣ = p ^ 2 - 1 := by
    rw [Nat.card_units, hcard]
  have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq p 1
  have hd : p + 1 ∣ p ^ 2 - 1 := by
    rw [hfactor]
    exact dvd_mul_left (p + 1) (p - 1)
  have hrootsCard : Nat.card (rootsOfUnity (p + 1) E) = p + 1 := by
    rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker,
      hcardUnits, Nat.gcd_eq_right hd]
  let := Fintype.ofFinite (rootsOfUnity (p + 1) E)
  by_contra h
  push Not at h
  have hf : Function.Injective (fun k : rootsOfUnity (p + 1) E => (k.val : E)) := by
    intro k l hkl
    exact Subtype.ext (Units.ext hkl)
  have heval : ∀ k : rootsOfUnity (p + 1) E,
      (-A).charpoly.eval (k.val : E) = 0 := by
    intro k
    simpa only [Matrix.eval_charpoly, sub_neg_eq_add] using h k
  have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (-A).charpoly hf heval (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
        ← Nat.card_eq_fintype_card, hrootsCard]
      omega)
  exact (Matrix.charpoly_monic (-A)).ne_zero hz

/-- Every ternary cocycle for quadratic finite-field conjugation has a linear
descent basis. The odd-prime hypotheses include characteristic three. -/
public theorem linear_cocycle_descent [Finite E]
    {p : ℕ} (hp : p.Prime) (hmod : p % 8 = 3)
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
  obtain ⟨k, hkdet⟩ := exists_norm_parameter hcard (by omega : 2 < p) A.val
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

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent
