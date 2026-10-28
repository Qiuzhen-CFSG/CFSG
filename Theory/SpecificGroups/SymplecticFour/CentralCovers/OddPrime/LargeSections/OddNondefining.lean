module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TransvectionLifts
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.Split
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.NonsplitTransfer
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.Nonsplit
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.Quartic
import Mathlib.Tactic.Ring

/-!
# Nondefining odd primes in symplectic four-space central kernels

The support p⁴−1 splits into p−1, p+1 and p²+1. The first two branches use
the actual split and quadratic norm-one product tori, with independent Weyl
inversion of one factor. In the quadratic case a norm correction makes the
Frobenius normalizer have determinant one. The quartic branch uses cyclic
Sylow subgroups, proved from the irreducible four-dimensional action of a
central subgroup of prime order. Transfer excludes each prime from the
literal kernel of any finite perfect central cover of Sp₄(Fₚ).

The final theorem discharges both geometric inputs to the retained conditional
assembly. It excludes every nondefining odd prime in this support for p > 3.
No characteristic-two hypothesis or assumed multiplier bound is used.

Source: Aschbacher–Smith I.1.1–4, printed pp.407–408; GLS3 §6.1,
Table 6.1.2's C₂ row and the absence of an exceptional multiplier for p≥5.
-/

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining

/-- Complete the prime exclusion from precisely the two missing geometric
inputs. The split-torus calculation and all three transfers are discharged. -/
public theorem not_dvd_card_kernel_of_nonsplit_inputs
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hr2 : r ≠ 2) (hd : r ∣ p^4 - 1)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    (hnonsplit : ∃ (ι : quadraticNormOne p × quadraticNormOne p →* Sp (ZMod p))
      (w : Sp (ZMod p)), Function.Injective ι ∧
      (∀ c : quadraticNormOne p, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ c : quadraticNormOne p, w * ι (1,c) * w⁻¹ = ι (1,c)))
    (hquartic : r ∣ p^2 + 1 → ∀ P : Sylow r (Sp (ZMod p)), IsCyclic P) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  have hf2 : p^2 - 1 = (p-1)*(p+1) := by
    simpa [mul_comm] using Nat.sq_sub_sq p 1
  have hf4 : p^4 - 1 = (p^2 - 1)*(p^2 + 1) := by
    have h := Nat.sq_sub_sq (p^2) 1
    simpa only [show (p^2)^2 = p^4 by ring, one_pow, mul_comm] using h
  rw [hf4, hf2] at hd
  rcases (Fact.out : r.Prime).dvd_mul.mp hd with hlinear | hquad
  · rcases (Fact.out : r.Prime).dvd_mul.mp hlinear with hminus | hplus
    · exact Split.not_dvd_card_kernel_of_dvd_sub_one hr2
        (by simpa only [Nat.card_zmod] using hminus) f
    · obtain ⟨ι, w, hi, hinv, hfix⟩ := hnonsplit
      exact NonsplitTransfer.not_dvd_card_kernel_of_product hr2
        (by simpa only [Nat.card_zmod] using hplus) ι hi
        (by simpa only [Nat.card_zmod] using card_quadraticNormOne p) w hinv hfix f
  · exact f.not_dvd_card_multiplier_of_isCyclic_sylow (hquartic hquad)

/-- Every nondefining odd prime in the support p⁴−1 is absent from the
kernel of a finite perfect central cover of the actual Sp₄(Fₚ), for p > 3.
This discharges the odd-prime input to `exists_section_of_prime_exclusions`. -/
public theorem not_dvd_card_kernel
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : 3 < p) (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p^4 - 1)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p))) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker :=
  not_dvd_card_kernel_of_nonsplit_inputs hr2 hd f
    (Nonsplit.exists_nonsplit_product p hp)
    (fun hquad => Quartic.sylow_isCyclic_of_dvd_sq_add_one hp hr2 hrp hquad)

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining
