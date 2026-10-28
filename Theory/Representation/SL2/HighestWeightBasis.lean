module

public import Theory.Representation.SL2.HighestWeightSpan
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of Highest-Weight Orbit Spans

For a field homomorphism `K -> F`, the span of the SL2(K)-orbit of `X 0 ^ n`
has dimension equal to the number of nonzero binomial coefficients in row `n`,
provided `K` has `n + 1` distinct elements. The finite-field corollary assumes
`n < |K|`. No characteristic restriction is otherwise needed.

Binomial expansion expresses each orbit vector in the span of the weighted
monomials `choose n r * X 0 ^ r * X 1 ^ (n-r)`. Conversely, matrices with first
column `(t, 1)` give sampled vectors whose coefficients are precisely these
weighted monomials; Vandermonde recovers them. Discarding zero coefficients
leaves independent monomials rescaled by nonzero field elements.

This is the representation-theoretic part of the digit-product dimensions in
Fong--Wong, Nagoya Math. J. 36 (1969), p. 149, formula (1.15). The conversion
from nonzero binomial coefficients to base-prime digit counts is separate.
-/

open MvPolynomial
open scoped MatrixGroups

namespace Representation.SL2

variable {K F : Type*} [Field K] [Field F]

private noncomputable def weightedMonomial (n : ℕ) (r : Fin (n + 1)) : MvPolynomial (Fin 2) F :=
  (n.choose r : F) • (X 0 ^ (r : ℕ) * X 1 ^ (n-r))

private theorem binomial_expansion (n : ℕ) (a b : F) :
    (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) F) ^ n =
      ∑ r : Fin (n+1), (a ^ (r : ℕ) * b ^ (n-r)) • weightedMonomial n r := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  simp only [weightedMonomial, mul_pow, Algebra.smul_def, map_mul, map_pow,
    map_natCast, MvPolynomial.algebraMap_eq]
  ring

private theorem action_X_pow (e : K →+* F) (n : ℕ) (g : SL(2, K)) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e g) (X 0 ^ n) =
      (C (e (g 0 0)) * X 0 + C (e (g 1 0)) * X 1) ^ n := by
  simp [polynomialAction, Fin.sum_univ_two]

private theorem highestWeightSpan_le_weighted (e : K →+* F) (n : ℕ) :
    (highestWeightSpan e n).toSubmodule ≤
      Submodule.span F (Set.range (weightedMonomial (F := F) n)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  dsimp only
  rw [action_X_pow, binomial_expansion]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

private def sampleMatrix (t : K) : SL(2, K) :=
  ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

private theorem weighted_mem_highestWeightSpan (e : K →+* F) (n : ℕ)
    (x : Fin (n+1) → K) (hx : Function.Injective x) (r : Fin (n+1)) :
    weightedMonomial (F := F) n r ∈ highestWeightSpan e n := by
  apply (highestWeightSpan e n).toSubmodule.coeff_mem_of_sum_pow_smul_mem
    (weightedMonomial n) (fun a => e (x a)) (e.injective.comp hx) _ r
  intro a
  have h : polynomialAction F (Matrix.SpecialLinearGroup.map e (sampleMatrix (x a))) (X 0 ^ n) ∈
      highestWeightSpan e n := Submodule.subset_span ⟨sampleMatrix (x a), rfl⟩
  rw [action_X_pow, binomial_expansion] at h
  change _ ∈ (highestWeightSpan e n).toSubmodule at h
  simpa [sampleMatrix] using h

private theorem highestWeightSpan_eq_weighted (e : K →+* F) (n : ℕ)
    (x : Fin (n+1) → K) (hx : Function.Injective x) :
    (highestWeightSpan e n).toSubmodule =
      Submodule.span F (Set.range (weightedMonomial (F := F) n)) := by
  apply le_antisymm (highestWeightSpan_le_weighted e n)
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact weighted_mem_highestWeightSpan e n x hx r

private theorem weighted_span_eq_admissible (n : ℕ) :
    Submodule.span F (Set.range (weightedMonomial (F := F) n)) =
      Submodule.span F (Set.range fun r : {r : Fin (n+1) // (n.choose r : F) ≠ 0} =>
        weightedMonomial n r.val) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    by_cases hr : (n.choose r : F) = 0
    · simp [weightedMonomial, hr]
    · exact Submodule.subset_span ⟨⟨r, hr⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    exact Submodule.subset_span ⟨r.val, rfl⟩

private theorem monomials_independent (n : ℕ) :
    LinearIndependent F (fun r : Fin (n+1) =>
      (X 0 ^ (r : ℕ) * X 1 ^ (n-r) : MvPolynomial (Fin 2) F)) := by
  let d : Fin (n+1) → Fin 2 →₀ ℕ := fun r =>
    Finsupp.equivFunOnFinite.symm ![r.val, n-r.val]
  have hd : Function.Injective d := by
    intro r s hrs
    apply Fin.ext
    have h := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hrs
    simpa [d] using h
  have h := (MvPolynomial.basisMonomials (Fin 2) F).linearIndependent.comp d hd
  have heq : (fun r : Fin (n+1) => (X 0 ^ (r : ℕ) * X 1 ^ (n-r) : MvPolynomial (Fin 2) F)) =
      (MvPolynomial.basisMonomials (Fin 2) F) ∘ d := by
    funext r
    simp [d, MvPolynomial.coe_basisMonomials, monomial_eq, Finsupp.prod_fintype,
      Fin.prod_univ_two]
  rw [heq]
  exact h

private theorem admissible_weighted_independent (n : ℕ) :
    LinearIndependent F (fun r : {r : Fin (n+1) // (n.choose r : F) ≠ 0} =>
      weightedMonomial (F := F) n r.val) := by
  have h := (monomials_independent (F := F) n).comp
    (fun r : {r : Fin (n+1) // (n.choose r : F) ≠ 0} => r.val) Subtype.val_injective
  have hu := h.units_smul (fun r => Units.mk0 (n.choose r.val : F) r.property)
  convert hu using 1
  funext r
  rfl

public theorem highestWeightSpan_finrank (e : K →+* F) (n : ℕ)
    (x : Fin (n+1) → K) (hx : Function.Injective x) :
    Module.finrank F (highestWeightSpan e n).toSubmodule =
      Nat.card {r : Fin (n+1) // (n.choose r : F) ≠ 0} := by
  classical
  rw [highestWeightSpan_eq_weighted e n x hx, weighted_span_eq_admissible,
    finrank_span_eq_card (admissible_weighted_independent n), Nat.card_eq_fintype_card]

public theorem highestWeightSpan_finrank_of_lt_card [Finite K] (e : K →+* F) (n : ℕ)
    (hn : n < Nat.card K) :
    Module.finrank F (highestWeightSpan e n).toSubmodule =
      Nat.card {r : Fin (n+1) // (n.choose r : F) ≠ 0} := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨x⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (n+1)) (β := K)
    (by simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using Nat.succ_le_of_lt hn)
  exact highestWeightSpan_finrank e n x x.injective

end Representation.SL2

