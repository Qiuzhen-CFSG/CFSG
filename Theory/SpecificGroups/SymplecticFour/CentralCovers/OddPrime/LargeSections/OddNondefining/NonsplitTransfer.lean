module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.Ring

/-!
# Transfer from a nonsplit product torus in symplectic four-space

A faithfully embedded product of cyclic groups of order q+1 has index
q⁴(q−1)²(q²+1) in the actual symplectic matrix group. For an odd prime
dividing q+1 this index is coprime to the prime. Independent inversion of
one factor therefore gives the abelian Sylow preimage required by transfer.

The torus embedding and inverter are explicit inputs here. In odd
characteristic their construction requires a determinant correction to the
quadratic Frobenius reflection; the even-field witness is not applicable.
Source: Aschbacher–Smith I.1.1–4, printed pp.407–408, and GLS3 §6.1.
-/

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining

/-- The actual norm-one torus of the quadratic extension of the prime field. -/
public noncomputable abbrev quadraticNormOne (p : ℕ) [Fact p.Prime] :=
  rootsOfUnity (p + 1) (FiniteField.Extension (ZMod p) p 2)

/-- Its order is p+1, also in odd characteristic. -/
public theorem card_quadraticNormOne (p : ℕ) [Fact p.Prime] :
    Nat.card (quadraticNormOne p) = p + 1 := by
  change Nat.card (rootsOfUnity (p + 1) (FiniteField.Extension (ZMod p) p 2)) = p + 1
  rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_units,
    FiniteField.natCard_extension, Nat.card_zmod]
  apply Nat.gcd_eq_right
  rw [show p^2 - 1 = (p - 1) * (p + 1) by
    simpa [mul_comm] using Nat.sq_sub_sq p 1]
  exact dvd_mul_left _ _

namespace NonsplitTransfer

/-- The nonsplit product torus, if constructed, excludes every odd divisor
of q+1 from a perfect central kernel, in any characteristic. -/
public theorem not_dvd_card_kernel_of_product
    {F : Type*} [Field F] [Finite F]
    {C : Type*} [CommGroup C] [Finite C] [IsCyclic C]
    {E : Type*} [Group E] [Finite E]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ∣ Nat.card F + 1)
    (ι : C × C →* Sp F) (hι : Function.Injective ι)
    (hc : Nat.card C = Nat.card F + 1) (w : Sp F)
    (hinv : ∀ c : C, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1))
    (hfix : ∀ c : C, w * ι (1,c) * w⁻¹ = ι (1,c))
    (f : PerfectCentralCovering.Cover E (Sp F)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  have hp : p.Prime := Fact.out
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hf2 : (Nat.card F)^2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
  have hf4 : (Nat.card F)^4 - 1 = ((Nat.card F)^2 - 1) * ((Nat.card F)^2 + 1) := by
    have h := Nat.sq_sub_sq ((Nat.card F)^2) 1
    simpa only [show ((Nat.card F)^2)^2 = (Nat.card F)^4 by ring,
      one_pow, mul_comm] using h
  have hcardT : Nat.card ι.range = (Nat.card F + 1)^2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, Nat.card_prod, hc, pow_two]
  have hi : ι.range.index = (Nat.card F)^4 * (Nat.card F - 1)^2 * ((Nat.card F)^2 + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.succ_pos (Nat.card F)) 2)
    rw [← hcardT, Subgroup.card_mul_index, Theory.SpecificGroups.SymplecticFour.card_sp, hf4, hf2, hcardT]
    ring
  have hnot2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hnotq : ¬ p ∣ Nat.card F := by
    intro h
    have hh := Nat.dvd_sub hd h
    rw [Nat.add_sub_cancel_left] at hh
    exact hp.not_dvd_one hh
  have hnotminus : ¬ p ∣ Nat.card F - 1 := by
    intro h
    have hh := Nat.dvd_sub hd h
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at hh
    exact hnot2 hh
  have hnotquad : ¬ p ∣ (Nat.card F)^2 + 1 := by
    intro h
    have hd' : p ∣ (Nat.card F)^2 - 1 := by rw [hf2]; exact dvd_mul_of_dvd_right hd _
    have hh := Nat.dvd_sub h hd'
    rw [show (Nat.card F)^2 + 1 - ((Nat.card F)^2 - 1) = 2 by
      have : 1 ≤ (Nat.card F)^2 := Nat.one_le_pow _ _ hq
      omega] at hh
    exact hnot2 hh
  have hpindex : ¬ p ∣ ι.range.index := by
    rw [hi]
    exact hp.not_dvd_mul
      (hp.not_dvd_mul (fun h => hnotq (hp.dvd_of_dvd_pow h))
        (fun h => hnotminus (hp.dvd_of_dvd_pow h))) hnotquad
  exact ProductTori.not_dvd_card_kernel_of_product_index hp2 ι hι hpindex w hinv hfix f

end NonsplitTransfer
end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining
