module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Inputs
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Spectrum.Certificate
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The balanced prime-order F4 spectrum bound

Choose the first nonidentity torus coordinate. For prime order it is a primitive
root, and every other coordinate is a power of it. Its own exponent is one and
all preceding exponents are zero. A coroot character is then the primitive root
raised to the integral pairing with its weight; it is fixed precisely when that
pairing is zero modulo the prime.

The finite certificate checks these normalized exponent vectors for five and
thirteen. We identify its linear forms with both literal weight tables, so equal
short and long fixed-character counts imply at most four fixed short characters.
This proves `PrimeSpectrumBound` over any field. Torus placement and the Ree
fixed-point equation supplying `ShortLongBalance` remain separate inputs to
`coverage_of_placement_balance_spectrum`.

Source: GLS3, Sections 1.8 and 1.14; the spectrum step used in Guralnick--Malle II,
Lemma 8.8 (internal p.57).
-/

public section

open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
open Spectrum

private def dot (a : Fin 4 → ℕ) (w : CorootWeight) : ℤ :=
  a 0 * w 0 + a 1 * w 1 + a 2 * w 2 + a 3 * w 3

private def exponentCount (p : ℕ) (a : Fin 4 → ℕ) (w : Fin 24 → CorootWeight) : ℕ :=
  (List.ofFn w).countP (fun μ => dot a μ % p == 0)

variable {F : Type*} [Field F] {p : ℕ}

private theorem character_pow (ζ : Fˣ) (a : Fin 4 → ℕ) (μ : CorootWeight) :
    corootCharacter (fun i => ζ ^ a i) μ = ζ ^ dot a μ := by
  simp only [corootCharacter, dot, zpow_add, zpow_mul, zpow_natCast]

private theorem count_eq (ζ : Fˣ) (hζ : IsPrimitiveRoot ζ p) (a : Fin 4 → ℕ)
    (w : Fin 24 → CorootWeight) :
    fixedWeightCount w (fun i => ζ ^ a i) = exponentCount p a w := by
  classical
  unfold fixedWeightCount exponentCount
  simp_rw [character_pow, hζ.zpow_eq_one_iff_dvd, Int.dvd_iff_emod_eq_zero]
  rw [← List.toFinset_finRange 24, (List.nodup_finRange 24).card_eq_countP]
  rw [List.ofFn_eq_map, List.countP_map]
  simp only [Function.comp_def, Bool.beq_eq_decide_eq]

private theorem powers (ζ : Fˣ) (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0)
    (t : Fˣ) (ht : t ^ p = 1) : ∃ a : Fin p, ζ ^ a.val = t := by
  let : NeZero p := ⟨hp⟩
  obtain ⟨a, ha, he⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p t).mpr ht)
  exact ⟨⟨a, ha⟩, he⟩

private def Normalized (a : Fin 4 → ℕ) : Prop :=
  ∃ j : Fin 4, a j = 1 ∧ ∀ i, i < j → a i = 0

private theorem normalized_powers (hp : p.Prime) (t : Fin 4 → Fˣ)
    (ht : t ≠ 1) (hpow : ∀ i, t i ^ p = 1) :
    ∃ (ζ : Fˣ) (a : Fin 4 → ℕ), IsPrimitiveRoot ζ p ∧
      (∀ i, a i < p) ∧ Normalized a ∧ t = fun i => ζ ^ a i := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hex : {i : Fin 4 | t i ≠ 1}.Nonempty := by
    by_contra h
    apply ht
    funext i
    simpa using (not_exists.mp h i)
  obtain ⟨j, hj, hmin⟩ := wellFounded_lt.has_min {i : Fin 4 | t i ≠ 1} hex
  have hζ : IsPrimitiveRoot (t j) p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (hpow j) hj)
  choose a ha using fun i => powers (t j) hζ hp.ne_zero (t i) (hpow i)
  refine ⟨t j, fun i => (a i).val, hζ, fun i => (a i).isLt, ⟨j, ?_, ?_⟩, ?_⟩
  · exact hζ.pow_inj (a j).isLt hp.one_lt (by simpa using ha j)
  · intro i hij
    have hi : t i = 1 := by
      by_contra hi
      exact hmin i hi hij
    exact hζ.pow_inj (a i).isLt hp.pos (by simpa [hi] using ha i)
  · funext i
    exact (ha i).symm

private theorem short_eval (a : Fin 4 → ℕ) :
    (List.ofFn EndNode.endOrbitWeight).map (dot a) =
      linearForms (a 0) (a 1) (a 2) (a 3) := by
  simp [List.ofFn_succ, dot, EndNode.endOrbitWeight, linearForms, sub_eq_add_neg,
    mul_comm]

private theorem long_eval (a : Fin 4 → ℕ) :
    (List.ofFn longOrbitWeight).map (dot a) =
      linearForms (2 * a 3) (2 * a 2) (a 1) (a 0) := by
  simp [List.ofFn_succ, dot, longOrbitWeight, EndNode.endOrbitWeight, linearForms,
    sub_eq_add_neg]
  ring_nf
  simp

private theorem exponentCount_short (p : ℕ) (a : Fin 4 → ℕ) :
    exponentCount p a EndNode.endOrbitWeight =
      shortCount p (a 0) (a 1) (a 2) (a 3) := by
  change (List.ofFn EndNode.endOrbitWeight).countP
    ((fun x : ℤ => x % (p : ℤ) == 0) ∘ dot a) = _
  rw [← List.countP_map, short_eval]
  rfl

private theorem exponentCount_long (p : ℕ) (a : Fin 4 → ℕ) :
    exponentCount p a longOrbitWeight =
      shortCount p (2 * a 3) (2 * a 2) (a 1) (a 0) := by
  change (List.ofFn longOrbitWeight).countP
    ((fun x : ℤ => x % (p : ℤ) == 0) ∘ dot a) = _
  rw [← List.countP_map, long_eval]
  rfl

/-- The finite balanced-spectrum input required by the torus-coverage assembly. -/
theorem primeSpectrumBound (F : Type*) [Field F] : PrimeSpectrumBound F := by
  intro p hp t ht hpow hb
  have hprime : p.Prime := by
    rcases hp with rfl | rfl <;> decide
  obtain ⟨ζ, a, hζ, ha, hn, rfl⟩ := normalized_powers hprime t ht hpow
  change fixedWeightCount EndNode.endOrbitWeight _ = fixedWeightCount longOrbitWeight _ at hb
  rw [count_eq ζ hζ, count_eq ζ hζ, exponentCount_short, exponentCount_long] at hb
  rw [count_eq ζ hζ, exponentCount_short]
  exact balanced_normalized_le_four p hp a ha hn hb

/-- Application to the movement condition on the literal positive coroot characters. -/
theorem endWeightMovement_of_shortLongBalance (p : ℕ) (hp : p = 5 ∨ p = 13)
    (t : Fin 4 → Fˣ) (ht : t ≠ 1) (hpow : ∀ i, t i ^ p = 1)
    (hb : ShortLongBalance t) : EndWeightMovement t :=
  (endWeightMovement_iff_fixedWeightCount_le t).mpr
    (primeSpectrumBound F p hp t ht hpow hb)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
