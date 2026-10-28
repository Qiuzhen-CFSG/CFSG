module
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.SpecificGroups.PrimeToFifteen.Suzuki
public import Theory.GroupTheory.TwoPrimeSolvable
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.AtlasPort.LinearGroups.ReeG2.Order
public import Theory.SpecificGroups.ThreeDivisibility.Exceptional

/-!
# Cyclic, alternating, Suzuki and small-derived prime exclusions

Prime cyclic carriers are solvable. Alternating groups contain a factor three
in their order, and Suzuki groups contain five. The small derived carriers
are handled by concrete cubic witnesses, the A₆ identification, and the
ternary Ree order formula: a three-free section of its order has only primes
two and seven and is solvable by Burnside. No simplicity certificate is needed.

Application: the full known-simple K hypothesis and Aschbacher–Smith D.2.13.
-/

public section
open Subgroup
namespace CFSG.KnownSimple.PrimeToFifteen

private theorem alternating_three_dvd (n : ℕ) (hn : 5 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have h : 6 ∣ n.factorial := by
    exact dvd_trans (by decide : 6 ∣ (3 : ℕ).factorial) (Nat.factorial_dvd_factorial (by omega))
  let : NeZero n := ⟨by omega⟩
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨k, hk⟩ := h
  rw [hk]
  omega

theorem solvable_of_primeCyclic {G : Type*} [Group G]
    (h : IsPrimeCyclicCarrier G) : Group.IsSolvable G := by
  obtain ⟨p, hp, ⟨e⟩⟩ := h
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem not_coprime_three_of_alternating {G : Type*} [Group G]
    {n : ℕ} (hn : 5 ≤ n) (e : G ≃* alternatingGroup (Fin n)) :
    ¬ Nat.Coprime 3 (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv]
  intro hc
  exact Nat.prime_three.coprime_iff_not_dvd.mp hc (alternating_three_dvd n hn)

theorem not_coprime_five_of_suzuki {G : Type*} [Group G]
    {m : ℕ} (hm : 1 ≤ m)
    (e : G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ¬ Nat.Coprime 5 (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv]
  exact (Nat.prime_five.coprime_iff_not_dvd).not.mpr
    (not_not.mpr (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_five_dvd m hm))

theorem solvable_of_smallDerived {G : Type*} [Group G] [Finite G]
    (h : IsSmallDerivedCarrier G) (h3 : Nat.Coprime 3 (Nat.card G))
    (_h5 : Nat.Coprime 5 (Nat.card G)) : Group.IsSolvable G := by
  cases h with
  | symplectic iso =>
    obtain ⟨e⟩ := iso
    let f := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    exact (not_coprime_three_of_alternating (by decide) f h3).elim
  | g2 iso =>
    obtain ⟨e⟩ := iso
    have hd := Theory.SpecificGroups.ThreeDivisibility.g2_derived
    rw [← Nat.card_congr e.toEquiv] at hd
    exact (Nat.prime_three.coprime_iff_not_dvd.mp h3 hd).elim
  | ree iso =>
    obtain ⟨e⟩ := iso
    have horder : Nat.card (Atlas.ReeG2.Model (ZMod 3) 0) = 1512 := by
      have h := Atlas.ReeG2.order (F := ZMod 3) 0 (by norm_num)
      norm_num at h
      exact h
    have hcard : Nat.card G ∣ 1512 := by
      rw [Nat.card_congr e.toEquiv]
      exact horder ▸ (commutator (Atlas.ReeG2.Model (ZMod 3) 0)).card_subgroup_dvd_card
    apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_prime G Nat.prime_seven
    intro p hp hd
    have hd' : p ∣ 1512 := hd.trans hcard
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact Nat.prime_three.coprime_iff_not_dvd.mp h3 hd
    have hfactor : 1512 = 2 ^ 3 * 3 ^ 3 * 7 := by norm_num
    rw [hfactor] at hd'
    rcases hp.dvd_mul.mp hd' with hd' | hd'
    · rcases hp.dvd_mul.mp hd' with hd' | hd'
      · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd')
      · exact (hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd'))).elim
    · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp hd'
  | tits iso =>
    obtain ⟨e⟩ := iso
    have hd := Theory.SpecificGroups.ThreeDivisibility.tits
    rw [← Nat.card_congr e.toEquiv] at hd
    exact (Nat.prime_three.coprime_iff_not_dvd.mp h3 hd).elim
end CFSG.KnownSimple.PrimeToFifteen
