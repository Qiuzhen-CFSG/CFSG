module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation
public import BenderSuzuki.External.Huppert.II.theorem_10_4
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Three-dimensional semilinear matrix descent

Let the field have order `q²`, with the stored Hermitian involution fixing
exactly `q` elements, and suppose `q = 2^n ≥ 4`. Every matrix cocycle
`A * conj(A) = 1` has an invertible matrix `P` with `A * conj(P) = P`.

The norm-one group has `q + 1 > 3` elements, so its elements cannot all be
roots of the cubic characteristic polynomial of `-A`. Choose a nonroot `k`
and construct a nonzero scalar `t` with `conj(t) * k = t`. Then
`P = t • 1 + conj(t) • A = conj(t) • (k • 1 + A)` is invertible, and the
cocycle identity gives the required descent equation. The scalar construction
includes `k = -1`, which equals `1` in characteristic two.

This adapts the checked parameter argument in
`OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.LinearCocycle`
to a nonprime fixed-field order. Huppert II.10.4 identifies the stored
involution with the `q`-power Frobenius. No unproved Hilbert–90 theorem or
conjugacy classification is used.

Source context: GLS3, Proposition 4.9.2(b2,g), and GLS4, Chapter 4,
Lemma 3.4(a,c). This is precisely the linear matrix premise in
`projective_descent_of_linear_descent_and_symmetric_forms`; unitary and
projective assembly remain in the parent development.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The elementary scalar Hilbert–90 parameterization includes `-1`. -/
private theorem linear_scalar_descent_parameter
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

/-- A cubic cannot vanish on all `q + 1` norm-one parameters. -/
private theorem linear_exists_norm_parameter [Finite E]
    {q : ℕ} (hcard : Nat.card E = q ^ 2) (hq : 2 < q)
    (A : Matrix (Fin 3) (Fin 3) E) :
    ∃ k : rootsOfUnity (q + 1) E,
      (Matrix.scalar (Fin 3) (k.val : E) + A).det ≠ 0 := by
  classical
  have hcardUnits : Nat.card Eˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hcard]
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq q 1
  have hd : q + 1 ∣ q ^ 2 - 1 := by
    rw [hfactor]
    exact dvd_mul_left (q + 1) (q - 1)
  have hrootsCard : Nat.card (rootsOfUnity (q + 1) E) = q + 1 := by
    rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker,
      hcardUnits, Nat.gcd_eq_right hd]
  let := Fintype.ofFinite (rootsOfUnity (q + 1) E)
  by_contra h
  push Not at h
  have hf : Function.Injective (fun k : rootsOfUnity (q + 1) E => (k.val : E)) := by
    intro k l hkl
    exact Subtype.ext (Units.ext hkl)
  have heval : ∀ k : rootsOfUnity (q + 1) E,
      (-A).charpoly.eval (k.val : E) = 0 := by
    intro k
    simpa only [Matrix.eval_charpoly, sub_neg_eq_add] using h k
  have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (-A).charpoly hf heval (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
        ← Nat.card_eq_fintype_card, hrootsCard]
      omega)
  exact (Matrix.charpoly_monic (-A)).ne_zero hz

/-- Every ternary cocycle over the quadratic field of order `(2^n)^2` has a
linear descent basis. This discharges exactly the `hlinear` premise of
`projective_descent_of_linear_descent_and_symmetric_forms`. -/
public theorem linear_cocycle_descent [Finite E]
    (n : ℕ) (hn : 2 ≤ n)
    (hE : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (A : GL (Fin 3) E)
    (hA : A * GeneralLinearGroup.map J.conj.toRingHom A = 1) :
    ∃ P : GL (Fin 3) E, A * GeneralLinearGroup.map J.conj.toRingHom P = P := by
  classical
  let q := 2 ^ n
  have hq : 2 < q := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  have hne : ∃ s : E, J.conj s ≠ s := by
    by_contra h
    push Not at h
    let e : {x : E // J.conj x = x} ≃ E :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, h x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Nat.card_congr e
    rw [hfixed, hE] at hc
    change q = q ^ 2 at hc
    nlinarith
  obtain ⟨k, hkdet⟩ := linear_exists_norm_parameter hE hq A.val
  have hkpow : (k.val : E) ^ (q + 1) = 1 :=
    (mem_rootsOfUnity' (q + 1) k.val).mp k.property
  have hknorm : J.conj (k.val : E) * (k.val : E) = 1 := by
    rw [BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hE hfixed]
    simpa only [pow_succ] using hkpow
  obtain ⟨t, ht0, ht⟩ := linear_scalar_descent_parameter J hne (k.val : E) hknorm
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

end BenderSuzuki.MatrixGroups.HermitianForm
