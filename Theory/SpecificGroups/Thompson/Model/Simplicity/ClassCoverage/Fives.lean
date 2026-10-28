module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Fives.Words

/-!
# Assembly of Thompson order-five cyclic coverage

Under the proposed ambient order, a subgroup of order 125 is Sylow. Thus
bijective coordinates on the fixed candidate subgroup, together with ambient
power-conjugacy witnesses for its 124 nonzero coordinates, suffice to cover
every order-five element by representative 4.

The two concrete certificate inputs below are explicit outstanding premises;
the final coverage result must discharge both. Source words and their
provenance are recorded in `Fives.Words` and `Fives/source/`.
-/

public section

namespace Thompson.Simplicity.Fives

open PrimeCyclicCoverage

/-- The proposed ambient order has exactly three factors of five. -/
theorem five_not_dvd_index
    (hcard : Nat.card Model = 90745943887872000)
    (P : Subgroup Model) (hP : Nat.card P = 125) : ¬ 5 ∣ P.index := by
  intro h
  have hd : 5 ^ 4 ∣ Nat.card Model := by
    rw [← P.card_mul_index, hP]
    exact Nat.mul_dvd_mul_left 125 h
  rw [hcard] at hd
  norm_num at hd

/-- Local coverage in a subgroup of order 125 transfers to the model. -/
theorem coverage_of_card_125
    (hcard : Nat.card Model = 90745943887872000)
    (P : Subgroup Model) (hP : Nat.card P = 125)
    (hlocal : ∀ y : Model, y ∈ P → orderOf y = 5 →
      ∃ k g, primeRepresentative 4 = g * y ^ k * g⁻¹) :
    CoversPrime primeRepresentative 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 3) hP
  apply prime_cyclic_coverage_of_sylow primeRepresentative
    (hp.toSylow (five_not_dvd_index hcard P hP))
  intro y hy ho
  obtain ⟨k, g, hg⟩ := hlocal y hy ho
  exact ⟨4, k, g, hg⟩

/-- Bijective coordinates certify the full five-part of the ambient order. -/
theorem localSubgroup_card_of_coordinates
    (hcoordinates : Function.Bijective normalFormElement) :
    Nat.card localSubgroup = 125 := by
  rw [← Nat.card_congr (Equiv.ofBijective normalFormElement hcoordinates)]
  simp

/-- Assemble the finite coordinate and fusion certificates. The ambient
order is the only other mathematical input. -/
theorem coverage_of_certificates
    (hcard : Nat.card Model = 90745943887872000)
    (hcoordinates : Function.Bijective normalFormElement)
    (hfusion : ∀ t : Coordinates, t ≠ (0, 0, 0) →
      ∃ (k : ℕ) (g : Model),
        primeRepresentative 4 = g * normalForm t ^ k * g⁻¹) :
    CoversPrime primeRepresentative 5 := by
  apply coverage_of_card_125 hcard localSubgroup
    (localSubgroup_card_of_coordinates hcoordinates)
  intro y hy ho
  obtain ⟨t, ht⟩ := hcoordinates.surjective ⟨y, hy⟩
  have hty := congrArg (fun w : localSubgroup => (w : Model)) ht
  change normalForm t = y at hty
  have ht0 : t ≠ (0, 0, 0) := by
    intro ht0
    rw [ht0, normalForm_zero] at hty
    rw [← hty, orderOf_one] at ho
    norm_num at ho
  simpa only [hty] using hfusion t ht0

/-- Separate the internal local-orbit calculation from the two ambient
bridges. Both can be certified independently against the fixed words. -/
theorem coverage_of_local_certificates
    (hcard : Nat.card Model = 90745943887872000)
    (hcoordinates : Function.Bijective normalFormElement)
    (hlocal : ∀ t : Coordinates, t ≠ (0, 0, 0) →
      ∃ (j : Fin 2) (k : ℕ) (g : Model),
        localRepresentative j = g * normalForm t ^ k * g⁻¹)
    (hbridge : ∀ j : Fin 2, ∃ (m : ℕ) (h : Model),
      primeRepresentative 4 = h * localRepresentative j ^ m * h⁻¹) :
    CoversPrime primeRepresentative 5 := by
  apply coverage_of_certificates hcard hcoordinates
  intro t ht
  obtain ⟨j, k, g, hg⟩ := hlocal t ht
  obtain ⟨m, h, hh⟩ := hbridge j
  refine ⟨k * m, h * g, ?_⟩
  rw [hh, hg, conj_pow, ← pow_mul]
  simp only [mul_inv_rev, mul_assoc]

end Thompson.Simplicity.Fives
