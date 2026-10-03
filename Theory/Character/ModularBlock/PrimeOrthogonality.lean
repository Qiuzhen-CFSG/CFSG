module

public import Theory.Character.ModularBlock.PrimeSelector
public import Theory.Character.ModularBlock.PrimeRegularTrace

/-!
# Column orthogonality in arbitrary-prime congruence blocks

For every ordinary congruence block at a prime `p`, the character column kernel
vanishes between a `p`-singular element and a `p`-regular element. The block is
specified by its central-character congruences, with no support assumption.

Map the mixed trace of the actual localized central idempotent into the complex
numbers. Its coefficient formula and Schur averaging identify this trace with
the block column kernel. The integral mixed-trace theorem makes it vanish.

Source: Brauer--Tuan, *On simple groups of finite order I* (1945), equation
(2.3). The Schur-averaging calculation follows `MixedConjugationTrace`.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.PrimeOrthogonality
open PrimeBlockConstruction MixedConjugationTrace BlockOrthogonality
attribute [local instance] Fintype.ofFinite
variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- The localized projector trace, mapped to the complex numbers, is the block
column kernel. The coefficient formula and Schur averaging identify the trace. -/
theorem localizedBlock_leftRight_trace
    (d : PrimeCongruenceBlockData p G) (j : d.I) (a b : G) :
    localizationToComplex d.primeIdeal
        (LinearMap.trace (Localization.AtPrime d.primeIdeal)
          (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
          (projectedLeftRight (PrimeSelector.localizedBlockElement d j) a b)) =
      ∑ i ∈ d.blockOf j, d.chi i (ConjClasses.mk a) *
        star (d.chi i (ConjClasses.mk b)) := by
  classical
  rw [trace_projectedLeftRight, map_sum]
  simp_rw [PrimeSelector.localizedBlockElement_coeff]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hchar (i : d.I) :
      (∑ x : G, d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk (x⁻¹ * a⁻¹ * x * b)⁻¹)) =
      (Nat.card G : ℂ) * (d.chi i (ConjClasses.mk a) *
        star (d.chi i (ConjClasses.mk b))) := by
    obtain ⟨n, rho, hrho⟩ := (d.complete.1 i).1
    let : Representation.IsIrreducible rho :=
      (irreducible_iff_character_norm_one (ρ := rho)).mpr
        (by simpa only [← hrho] using (d.complete.1 i).2)
    rw [hrho, ← Finset.mul_sum]
    change rho.character 1 * (∑ x : G, rho.character (x⁻¹ * a⁻¹ * x * b)⁻¹) =
      (Nat.card G : ℂ) * (rho.character a * star (rho.character b))
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using
      degree_mul_sum_character_mixed rho a b
  simp_rw [hchar]
  rw [← Finset.mul_sum]
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- Prime-singular and prime-regular character columns are orthogonal within
every ordinary congruence block. The actual localized projector supplies the
integral trace to which prime-regular trace vanishing applies. -/
theorem block_column_eq_zero_of_singular_regular
    [Fact p.Prime] (d : PrimeCongruenceBlockData p G) (j : d.I)
    (a b : G) (ha : p ∣ orderOf a) (hb : ¬ p ∣ orderOf b) :
    ∑ i ∈ d.blockOf j, d.chi i (ConjClasses.mk a) *
      star (d.chi i (ConjClasses.mk b)) = 0 := by
  have ht := PrimeRegularTrace.trace_projectedLeftRight_eq_zero p
    (PrimeSelector.prime_not_isUnit d) (PrimeSelector.exists_localization_primitiveRoot d)
    (PrimeSelector.localizedBlockElement d j)
    (PrimeSelector.localizedBlockElement_isIdempotent d j)
    (PrimeSelector.localizedBlockElement_mem_center d j) a b ha hb
  rw [← localizedBlock_leftRight_trace, ht, map_zero]

end ModularBlock.PrimeOrthogonality
