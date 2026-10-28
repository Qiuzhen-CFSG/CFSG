module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Separation of embedded finite-field Frobenius coefficients

The powers of Frobenius below the extension degree are distinct multiplicative
characters. Dedekind independence therefore extracts every vector coefficient
from their sums, including after passage to an arbitrary subspace quotient.
No algebraic closure or dimension bound on the target vector space is needed.

This is the finite coefficient step in Steinberg, *Representations of Algebraic
Groups*, Nagoya Math. J. 22 (1963), proofs of 5.1 and 12.2, pp.43 and 54–55.
-/

public section

open scoped BigOperators

namespace FiniteField

variable {p : ℕ} [Fact p.Prime]
variable {E F : Type*} [Field E] [Finite E] [Algebra (ZMod p) E] [Field F]

theorem embedded_frobenius_linearIndependent (f : E →+* F) :
    LinearIndependent F (fun i : Fin (Module.finrank (ZMod p) E) =>
      fun t : E => f (t ^ (p ^ i.val))) := by
  let φ := frobeniusAlgHom (ZMod p) E
  have hval (i : ℕ) (t : E) : (φ ^ i) t = t ^ (p ^ i) := by
    simp only [φ, AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  let χ (i : Fin (Module.finrank (ZMod p) E)) : E →* F :=
    f.toMonoidHom.comp (φ ^ i.val).toRingHom.toMonoidHom
  have hχ : Function.Injective χ := by
    intro i j h
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := φ)
    · simpa only [Set.mem_Iio, φ, orderOf_frobeniusAlgHom] using i.isLt
    · simpa only [Set.mem_Iio, φ, orderOf_frobeniusAlgHom] using j.isLt
    · ext t
      exact f.injective (DFunLike.congr_fun h t)
  have he : (fun i => (χ i : E → F)) =
      (fun i : Fin (Module.finrank (ZMod p) E) => fun t => f (t ^ (p ^ i.val))) := by
    funext i t
    exact congrArg f (hval i.val t)
  rw [← he]
  exact (linearIndependent_monoidHom E F).comp χ hχ

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem frobenius_coefficients_mem (f : E →+* F) (U : Submodule F V)
    (v : Fin (Module.finrank (ZMod p) E) → V)
    (h : ∀ t : E, ∑ i, f (t ^ (p ^ i.val)) • v i ∈ U) :
    ∀ i, v i ∈ U := by
  intro i
  rw [← Submodule.Quotient.mk_eq_zero]
  apply (Module.forall_dual_apply_eq_zero_iff F _).mp
  intro ℓ
  have hh : ∑ j, ℓ (U.mkQ (v j)) • (fun t : E => f (t ^ (p ^ j.val))) = 0 := by
    funext t
    have hx := congrArg ℓ ((Submodule.Quotient.mk_eq_zero U).mpr (h t))
    change ℓ (U.mkQ (∑ j, f (t ^ (p ^ j.val)) • v j)) = ℓ 0 at hx
    simpa only [map_sum, map_smul, map_zero, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_comm] using hx
  exact linearIndependent_iff'.mp (embedded_frobenius_linearIndependent f)
    Finset.univ (fun j => ℓ (U.mkQ (v j))) hh i (Finset.mem_univ i)

/-- Sampling the Frobenius sums spans exactly their vector coefficients. -/
theorem span_frobenius_sums (f : E →+* F)
    (v : Fin (Module.finrank (ZMod p) E) → V) :
    Submodule.span F (Set.range (fun t : E => ∑ i, f (t ^ (p ^ i.val)) • v i)) =
      Submodule.span F (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply frobenius_coefficients_mem f _ v _ i
    intro t
    exact Submodule.subset_span ⟨t, rfl⟩

end FiniteField
