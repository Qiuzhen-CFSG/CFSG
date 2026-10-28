module

public import Theory.Representation.SL2.CoefficientTwist
public import Theory.Representation.SL2.HighestWeightUnique
public import Theory.FieldTheory.SpanningFrobeniusPeriod
public import Theory.Representation.IrreducibleTraceEquivalence

/-!
# Frobenius Period of a Highest-Weight Trace Field

Suppose the character of an actual highest-weight orbit span over an
algebraically closed coefficient field comes from a finite subfield E, and its
values span E over the prime field. If the matrix field K has order p^m and
the highest weight n is less than |K|, then s = [E : GF(p)] divides m and
|K| - 1 divides n * (p^s - 1). The given trace data will come from the actual
endomorphism-field representation after scalar extension.

The m-th Frobenius fixes the embedding of K. The coefficient-twist formula
therefore fixes all trace values, so their spanning property forces s to
divide m. Conversely, Frobenius s fixes E and hence the character. Equality
of irreducible trace characters gives an actual equivalence to the coefficient
twist. Comparing the highest-weight diagonal eigenvalues on a generator of
K's unit group gives the second divisibility.

This supplies the period constraint in the argument after Fong--Wong (1.15),
Nagoya Math. J. 36 (1969), p. 149. Digit periodicity and the dimension estimates
are proved separately.
-/

open scoped MatrixGroups

namespace Representation.SL2

variable {K E F : Type*} [Field K] [Finite K] [Field E] [Finite E]
    [Field F] [IsAlgClosed F] [Algebra E F]
    (p : ℕ) [Fact p.Prime] [CharP F p] [Algebra (ZMod p) E]

private theorem period_dvd (e : K →+* F) (n m : ℕ) (hcard : Nat.card K = p ^ m)
    (τ : SL(2,K) → E) (hspan : Submodule.span (ZMod p) (Set.range τ) = ⊤)
    (hchar : ∀ g, (highestWeightSpan e n).toRepresentation.character g = algebraMap E F (τ g)) :
    Module.finrank (ZMod p) E ∣ m := by
  apply (FiniteField.forall_pow_eq_self_iff_finrank_dvd_of_span p τ hspan m).mp
  intro g
  apply (algebraMap E F).injective
  rw [map_pow, ← hchar]
  let σ := iterateFrobeniusEquiv F p m
  have he : (σ : F →+* F).comp e = e := by
    ext a
    change (e a) ^ (p ^ m) = e a
    rw [← map_pow, ← hcard]
    congr 1
    let : Fintype K := Fintype.ofFinite K
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a
  have h := highestWeightSpan_character_comp_embedding σ e n g
  rw [he] at h
  exact h.symm

private theorem weight_period (e : K →+* F) (n : ℕ) (hn : n < Nat.card K)
    (τ : SL(2,K) → E) (hspan : Submodule.span (ZMod p) (Set.range τ) = ⊤)
    (hchar : ∀ g, (highestWeightSpan e n).toRepresentation.character g = algebraMap E F (τ g)) :
    (Nat.card K - 1) ∣ n * (p ^ Module.finrank (ZMod p) E - 1) := by
  let s := Module.finrank (ZMod p) E
  let σ := iterateFrobeniusEquiv F p s
  have hfix : ∀ g, τ g ^ (p ^ s) = τ g :=
    (FiniteField.forall_pow_eq_self_iff_finrank_dvd_of_span p τ hspan s).mpr (dvd_refl s)
  have hχ : (highestWeightSpan e n).toRepresentation.character =
      (highestWeightSpan ((σ : F →+* F).comp e) n).toRepresentation.character := by
    funext g
    rw [highestWeightSpan_character_comp_embedding σ e n g, hchar]
    change algebraMap E F (τ g) = algebraMap E F (τ g) ^ (p ^ s)
    rw [← map_pow, hfix]
  let : IsIrreducible (highestWeightSpan e n).toRepresentation :=
    highestWeightSpan_isIrreducible_of_lt_card e n hn
  let : IsIrreducible (highestWeightSpan ((σ : F →+* F).comp e) n).toRepresentation :=
    highestWeightSpan_isIrreducible_of_lt_card ((σ : F →+* F).comp e) n hn
  obtain ⟨φ⟩ := (Representation.character_eq_iff_equiv_of_irreducible _ _).mp hχ
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hw := (highestWeightSpan_equiv_embedding_weights e ((σ : F →+* F).comp e) n n hn hn φ).1 a a.ne_zero
  change (e a) ^ n = ((e a) ^ (p ^ s)) ^ n at hw
  rw [← pow_mul, mul_comm (p ^ s)] at hw
  have he : a ^ n = a ^ (n * p ^ s) := Units.ext ((e.injective (by
    simpa only [Units.val_pow_eq_pow_val, map_pow] using hw)))
  have hd := (pow_eq_pow_iff_modEq.mp he).dvd'
  rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units] at hd
  simpa only [Nat.mul_sub_left_distrib, mul_one] using hd

public theorem highestWeightSpan_traceField_period (e : K →+* F) (n m : ℕ)
    (hn : n < Nat.card K) (hcard : Nat.card K = p ^ m)
    (τ : SL(2,K) → E) (hspan : Submodule.span (ZMod p) (Set.range τ) = ⊤)
    (hchar : ∀ g, (highestWeightSpan e n).toRepresentation.character g = algebraMap E F (τ g)) :
    Module.finrank (ZMod p) E ∣ m ∧
      (Nat.card K - 1) ∣ n * (p ^ Module.finrank (ZMod p) E - 1) :=
  ⟨period_dvd p e n m hcard τ hspan hchar, weight_period p e n hn τ hspan hchar⟩

end Representation.SL2
