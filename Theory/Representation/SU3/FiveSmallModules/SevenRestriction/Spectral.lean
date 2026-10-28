module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Inputs
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.RepresentationTheory.Invariants

/-!
# Integer fixed dimensions from the order-seven characteristic polynomial

An operator of order prime to the coefficient characteristic is semisimple.
Consequently the algebraic multiplicity of the root one is the dimension of
its fixed space, over the original field without a splitting-field assumption.
For the small unitary modules the polynomial `sevenSpectrum K d` therefore
gives fixed dimension `d - 18` and displacement 18.

This is the linear-algebra step in Guralnick–Malle, *Classification of
2F-modules I*, Proposition 4.3, pp.10–11. The concrete spectral polynomial
remains a hypothesis; no characteristic-two trace is substituted for it.
-/

public section

open Polynomial Subgroup Representation

namespace Representation.SU3.FiveSmallModules.SevenRestriction

variable {K R U : Type*} [Field K] [Group R] [AddCommGroup U] [Module K U]

/-- Intertwining equivalences preserve operator orders. Keeping this lemma
abstract avoids unfolding concrete induced-module quotients at its use sites. -/
theorem operator_order_eq_of_equiv
    {W : Type*} [AddCommGroup W] [Module K W]
    {τ : Representation K R U} {σ : Representation K R W}
    (e : τ.Equiv σ) (x : R) : orderOf (σ x) = orderOf (τ x) := by
  have h := e.toLinearEquiv.conjRingEquiv.toMulEquiv.orderOf_eq (τ x)
  change orderOf (e.toLinearEquiv.conj (τ x)) = orderOf (τ x) at h
  rwa [Representation.Equiv.conj_apply_self] at h

/-- The characteristic polynomial is preserved by the actual intertwiner. -/
theorem charpoly_eq_of_equiv
    {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K U] [FiniteDimensional K W]
    {τ : Representation K R U} {σ : Representation K R W}
    (e : τ.Equiv σ) (x : R) : (τ x).charpoly = (σ x).charpoly := by
  have h := e.toLinearEquiv.charpoly_conj (τ x)
  rw [Representation.Equiv.conj_apply_self] at h
  exact h.symm

/-- Cyclic invariants are the eigenspace for the eigenvalue one. -/
theorem invariants_zpowers_eq_eigenspace (τ : Representation K R U) (x : R) :
    invariants (τ.comp (zpowers x).subtype) = Module.End.eigenspace (τ x) 1 := by
  ext v
  rw [Module.End.mem_eigenspace_iff, one_smul]
  apply Representation.mem_invariants_iff_of_forall_mem_zpowers
    (τ.comp (zpowers x).subtype) ⟨x, mem_zpowers x⟩
  intro y
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp y.property
  exact mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

/-- A coprime-order operator has fixed dimension equal to the integer
multiplicity of one in its characteristic polynomial. -/
theorem finrank_invariants_eq_rootMultiplicity [FiniteDimensional K U]
    (τ : Representation K R U) (x : R) {n : ℕ}
    (hn : (n : K) ≠ 0) (hx : τ x ^ n = 1) :
    Module.finrank K (invariants (τ.comp (zpowers x).subtype)) =
      (τ x).charpoly.rootMultiplicity 1 := by
  have hs : Module.End.IsSemisimple (τ x) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := (X : K[X]) ^ n - 1)
    · exact (X_pow_sub_one_separable_iff.mpr hn).squarefree
    · simp [hx]
  rw [invariants_zpowers_eq_eigenspace,
    ← hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    LinearMap.finrank_maxGenEigenspace_eq]

/-- Extract the fixed dimension from a factorization at the root one. -/
theorem fixed_dimension_of_charpoly [FiniteDimensional K U]
    (τ : Representation K R U) (x : R) {n r : ℕ} (P : K[X])
    (hn : (n : K) ≠ 0) (hx : τ x ^ n = 1)
    (hP : P.eval 1 ≠ 0)
    (hc : (τ x).charpoly = P * (X - C 1) ^ r) :
    Module.finrank K (invariants (τ.comp (zpowers x).subtype)) = r := by
  rw [finrank_invariants_eq_rootMultiplicity τ x hn hx, hc,
    rootMultiplicity_mul_X_sub_C_pow (fun h => hP (by simp [h])),
    rootMultiplicity_eq_zero hP, zero_add]

/-- The concrete seven-spectrum has precisely the required fixed dimension. -/
theorem fixed_dimension_of_sevenSpectrum [CharP K 2] [FiniteDimensional K U]
    (τ : Representation K R U) (x : R) (hx : orderOf (τ x) = 7)
    (hc : (τ x).charpoly = sevenSpectrum K (Module.finrank K U)) :
    Module.finrank K (invariants (τ.comp (zpowers x).subtype)) =
      Module.finrank K U - 18 := by
  have h7 : (7 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 2 7).not.mpr (by decide)
  have hv : (sevenPolynomial K).eval 1 = (7 : K) := by
    norm_num [sevenPolynomial]
  have hp : (sevenPolynomial K ^ 3).eval 1 ≠ 0 := by
    rw [eval_pow, hv]
    exact pow_ne_zero 3 h7
  have hxpow : τ x ^ (7 : ℕ) = 1 := by
    simpa only [hx] using pow_orderOf_eq_one (τ x)
  exact fixed_dimension_of_charpoly τ x (sevenPolynomial K ^ 3) h7 hxpow hp hc

/-- The actual quotient by cyclic invariants has dimension 18 in both source
degrees, once the characteristic polynomial has been established. -/
theorem displacement_of_sevenSpectrum [CharP K 2] [FiniteDimensional K U]
    (τ : Representation K R U) (x : R) (hx : orderOf (τ x) = 7)
    (hd : Module.finrank K U = 20 ∨ Module.finrank K U = 21)
    (hc : (τ x).charpoly = sevenSpectrum K (Module.finrank K U)) :
    Module.finrank K (U ⧸ invariants (τ.comp (zpowers x).subtype)) = 18 := by
  have hf := fixed_dimension_of_sevenSpectrum τ x hx hc
  have hdim := Submodule.finrank_quotient_add_finrank
    (invariants (τ.comp (zpowers x).subtype))
  omega

end Representation.SU3.FiveSmallModules.SevenRestriction
