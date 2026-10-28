module

public import Theory.Representation.ReeF4.BinaryDegree.PeriodicProduct
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent

/-!
# From exceptional tensor factors to binary degree

This module specifies the part of the exceptional tensor classification used
in a degree estimate. The absolute dimension is the product of positive
factor dimensions over the field exponent. One factor is large. Frobenius
fixes the character after that exponent, and every Frobenius period of the
character is also a period of the factor dimensions.

The actual Schur degree therefore divides the field exponent. Its Frobenius
fixes the character, so the factor sequence repeats in blocks of that length.
`PeriodicProduct` bounds the block product; the scalar-dimension tower gives
the binary estimate. This proves the descent implication, not the existence
of the tensor factors for Ree groups.

Source: GLS3, Corollary 2.8.6(b) and Remark 2.8.8; Aschbacher--Smith,
*The Classification of Quasithin Groups*, printed p.356 (PDF p.367).
-/

public section

namespace Representation.FrobeniusTensor

universe u v w

/-- The dimension and character consequences to be constructed from an actual
exceptional tensor decomposition. No binary degree bound is a field of this
structure. For Ree groups the sequence records the dimensions of the basic
factors, in the cyclic order induced by ordinary Frobenius. -/
structure TraceTensorData {F : Type v} [Field F] {G : Type u} [Group G]
    {W : Type w} [AddCommGroup W] [Module F W]
    (n b : ℕ) (σ : Representation F G W) where
  /-- Dimensions of the basic factors, extended periodically. -/
  factorDegree : ℕ → ℕ
  /-- Every tensor factor is nonzero. -/
  factor_pos : ∀ i, 0 < factorDegree i
  /-- A nontrivial basic factor has the required absolute minimum. -/
  large_factor : ∃ i, b ≤ factorDegree i
  /-- The tensor-product dimension formula. -/
  finrank_eq : Module.finrank F W = ∏ i ∈ Finset.range n, factorDegree i
  /-- The field of size `2^n` splits this absolute representation. -/
  character_fixed : ∀ g, σ.character g ^ (2 ^ n) = σ.character g
  /-- Frobenius invariance of the character forces repetition of the basic
  factor dimensions; its proof uses uniqueness of the tensor parameters. -/
  factor_period : ∀ r, (∀ g, σ.character g ^ (2 ^ r) = σ.character g) →
    Function.Periodic factorDegree r

/-- The full descent implication, using the actual Schur field. The tensor
data remains a separate representation-theoretic premise. -/
theorem binary_finrank_ge_of_traceTensorData
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    {n b : ℕ} (hn : 0 < n) (hb : 2 ≤ b)
    (h : TraceTensorData n b (absoluteRep ρ)) :
    b * n ≤ Module.finrank (ZMod 2) V := by
  let s := Module.finrank (ZMod 2) (SchurField ρ)
  have hs : 0 < s := schurField_finrank_pos ρ
  have hsn : s ∣ n := (character_pow_iff ρ n).mp h.character_fixed
  obtain ⟨t, hnt⟩ := hsn
  have ht : 0 < t := by
    by_contra! hz
    have : t = 0 := Nat.eq_zero_of_le_zero hz
    simp only [this, mul_zero] at hnt
    omega
  have hperiod : Function.Periodic h.factorDegree s :=
    h.factor_period s ((character_pow_iff ρ s).mpr (dvd_refl s))
  have hbound := mul_prod_range_ge hs ht hb hperiod h.factor_pos h.large_factor
  rw [← hnt] at hbound
  rw [binary_finrank_eq ρ, h.finrank_eq]
  exact hbound

end Representation.FrobeniusTensor
