module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Frobenius periods of spanning families

If a family spans a finite extension of the prime field as a vector space,
its elements are all fixed by the sth power of Frobenius exactly when the
extension degree divides s. The index type is arbitrary, and s=0 is included.
The theorem uses the caller's existing algebra structure over ZMod p.

Frobenius is linear over the prime field, so agreement with the identity
on a spanning family is agreement everywhere. Mathlib's finite-field
Frobenius order theorem identifies its order with the extension degree.
Applied to the spanning traces of an endomorphism-field representation,
this relates trace period to Schur-field degree in finite-field descent.
-/

namespace FiniteField

public theorem forall_pow_eq_self_iff_finrank_dvd_of_span
    (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [Finite E]
    [Algebra (ZMod p) E] {ι : Type*} (τ : ι → E)
    (hspan : Submodule.span (ZMod p) (Set.range τ) = ⊤) (s : ℕ) :
    (∀ i, τ i ^ (p ^ s) = τ i) ↔ Module.finrank (ZMod p) E ∣ s := by
  let f := frobeniusAlgHom (ZMod p) E
  have happly (x : E) : (f ^ s) x = x ^ (p ^ s) := by
    simp only [f, AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have heq : (∀ i, τ i ^ (p ^ s) = τ i) ↔ f ^ s = 1 := by
    constructor
    · intro h
      have hl : (f ^ s).toLinearMap = (1 : E →ₐ[ZMod p] E).toLinearMap := by
        apply LinearMap.ext_on_range hspan
        intro i
        simpa only [AlgHom.toLinearMap_apply, AlgHom.one_apply, happly] using h i
      ext x
      exact DFunLike.congr_fun hl x
    · intro h i
      simpa only [happly, AlgHom.one_apply] using DFunLike.congr_fun h (τ i)
  rw [heq, ← orderOf_dvd_iff_pow_eq_one, orderOf_frobeniusAlgHom]

end FiniteField
