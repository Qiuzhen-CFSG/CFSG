module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.Transfer
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CentralCover

/-!
# Split-prime kernels of even symplectic four-space covers

For odd p dividing q−1 the concrete flag Borel has index
(q+1)²(q²+1), prime to p. Its full preimage in a finite central extension
is abelian modulo its two-core, by the independent Weyl inversion proved
in `EvenBorelTorus.CentralCover`. Transfer now excludes p from the kernel
of a perfect central cover. This includes the field of order four.

Source: Aschbacher–Smith, I.1.2–I.1.3, printed p.407, citing GLS98 §6.1.
-/

open Subgroup
open scoped IsMulCommutative

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
variable {F : Type*} [Field F] [Finite F]

/-- The index of the actual flag Borel, factored into its nonsplit parts. -/
public theorem index_borel : (borel (F := F)).index =
    (Nat.card F + 1)^2 * ((Nat.card F)^2 + 1) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hfactor (q : ℕ) (hq : 1 ≤ q) : q^2 - 1 = (q-1)*(q+1) := by
    have h1 := Nat.sub_add_cancel hq
    have h2 := Nat.sub_add_cancel (show 1 ≤ q^2 by nlinarith)
    nlinarith
  have hsub : 0 < Nat.card F - 1 := by omega
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hf2 := hfactor (Nat.card F) (by omega)
  have hf4 : (Nat.card F)^4 - 1 = ((Nat.card F)^2 - 1) * ((Nat.card F)^2 + 1) := by
    calc
      (Nat.card F)^4 - 1 = ((Nat.card F)^2)^2 - 1 := by congr 1; ring
      _ = _ := hfactor ((Nat.card F)^2) (by nlinarith)
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (Nat.card F)^4 * (Nat.card F - 1)^2 by positivity)
  rw [← card_borel, Subgroup.card_mul_index, card_sp, card_borel]
  simp only [hf4, hf2]
  ring

/-- An odd divisor of q−1 is prime to the Borel index. -/
public theorem not_dvd_index_borel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ Nat.card F - 1) : ¬ p ∣ (borel (F := F)).index := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hnot : ¬ p ∣ 2 := fun h => hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hplus : ¬ p ∣ Nat.card F + 1 := by
    intro h
    have hh := Nat.dvd_sub h hd
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at hh
    exact hnot hh
  have hsq : p ∣ (Nat.card F)^2 - 1 := by
    have he : (Nat.card F)^2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      have h1 := Nat.sub_add_cancel hq
      have h2 := Nat.sub_add_cancel (show 1 ≤ (Nat.card F)^2 by nlinarith)
      nlinarith
    rw [he]
    exact dvd_mul_of_dvd_left hd _
  have hsqplus : ¬ p ∣ (Nat.card F)^2 + 1 := by
    intro h
    have hh := Nat.dvd_sub h hsq
    rw [show (Nat.card F)^2 + 1 - ((Nat.card F)^2 - 1) = 2 by
      have : 1 ≤ (Nat.card F)^2 := by nlinarith
      omega] at hh
    exact hnot hh
  rw [index_borel]
  exact hp.not_dvd_mul (fun h => hplus (hp.dvd_of_dvd_pow h)) hsqplus

/-- Split-torus primes do not divide any finite perfect central kernel. -/
public theorem not_dvd_card_kernel_of_dvd_sub_one [CharP F 2]
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ∣ Nat.card F - 1)
    (f : E →* Sp F) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ p ∣ Nat.card f.ker := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hn' : Nat.card F = 2 ^ (n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  apply PerfectCentralCovering.not_dvd_card_kernel_of_two_core_quotient hp2 f hk
    (borel.comap f)
  · rw [Subgroup.index_comap_of_surjective _ hf]
    exact not_dvd_index_borel Fact.out hp2 hd
  · exact EvenBorelTorus.CentralCover.full_preimage_quotient_abelian hn' f hf hk

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
