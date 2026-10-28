module
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.FieldTheory.Separable

/-!
# Prime-to-characteristic matrices with one generalized eigenvalue

A matrix of finite order prime to the field characteristic is scalar if
subtracting that scalar gives a nilpotent matrix. Indeed X^n-1 is separable,
so its annihilated linear endomorphism is semisimple. Scalar subtraction
preserves semisimplicity, and nilpotent semisimple endomorphisms vanish.

This isolates the repeated-root step of the SL2 p-regular trace-class count.
The statement works for every finite matrix size and does not require the
coefficient field itself to be finite.
-/

namespace Matrix

public theorem eq_scalar_of_isNilpotent_sub_of_pow_eq_one
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {p n : ℕ} [CharP K p] (A : Matrix ι ι K) (r : K)
    (hn : ¬ p ∣ n) (hpow : A ^ n = 1) (hnil : IsNilpotent (A - r • 1)) :
    A = r • 1 := by
  let e : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K) := Matrix.toLinAlgEquiv'
  have hs : (e A).IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C' p n (1 : K) hn one_ne_zero).squarefree
    simp only [map_sub, Polynomial.aeval_X_pow, map_one]
    rw [← map_pow, hpow, map_one, sub_self]
  have hs' : (e A - algebraMap K (Module.End K (ι → K)) r).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.mpr hs
  have hn' : IsNilpotent (e A - algebraMap K (Module.End K (ι → K)) r) := by
    obtain ⟨m, hm⟩ := hnil
    refine ⟨m, ?_⟩
    have h := congrArg e hm
    simpa only [map_pow, map_sub, map_smul, map_one, map_zero, Algebra.algebraMap_eq_smul_one]
      using h
  have hz := Module.End.eq_zero_of_isNilpotent_isSemisimple hn' hs'
  apply e.injective
  simpa only [map_smul, map_one, Algebra.algebraMap_eq_smul_one] using sub_eq_zero.mp hz

end Matrix
