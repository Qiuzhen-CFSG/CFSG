module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Prime support of a perfect central kernel over Sp₄(3)

The actual matrix group has order 2⁷ · 3⁴ · 5. For every prime other than
two and three, a Sylow subgroup has order dividing five, hence is cyclic.
Central Sylow transfer then excludes that prime from the kernel of every
finite perfect central cover, including primes absent from the group order.
Consequently only the two-primary and three-primary calculations remain.

The consumer is `TernarySection.exists_section_of_not_two_dvd_of_not_three_dvd`,
which uses this exclusion to prove that the covering map is an isomorphism.
No assertion about the two-primary or three-primary kernel is made here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.1.2
and I.1.4(1), printed pp.407–408; GLS3 §6.1. The U₄(2) entry of I.1.4(1)
is the projective ternary symplectic endpoint. This proof uses the actual
symplectic group order and transfer, without presuming a unitary comparison
or the source multiplier table.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection

/-- Specialize the hyperbolic-pair counting formula to the literal ternary
symplectic matrix group. -/
theorem card_sp_three : Nat.card (OddPrime.Sp (ZMod 3)) = 51840 := by
  simpa using Theory.SpecificGroups.SymplecticFour.card_sp (ZMod 3)

/-- Away from two and three, the Sylow order divides the remaining factor five. -/
theorem sylow_card_dvd_five_of_ne_two_ne_three {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (P : Sylow p (OddPrime.Sp (ZMod 3))) :
    Nat.card P ∣ 5 := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  have h2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
    simpa only [Nat.dvd_prime Nat.prime_two, hp.ne_one, false_or] using hp2)
  have h3 : p.Coprime 3 := hp.coprime_iff_not_dvd.mpr (by
    simpa only [Nat.dvd_prime Nat.prime_three, hp.ne_one, false_or] using hp3)
  have hc : (Nat.card P).Coprime (2 ^ 7 * 3 ^ 4) := by
    rw [hm]
    exact ((h2.pow_right 7).mul_right (h3.pow_right 4)).pow_left m
  apply hc.dvd_of_dvd_mul_left
  have hd := (P : Subgroup (OddPrime.Sp (ZMod 3))).card_subgroup_dvd_card
  norm_num [card_sp_three] at hd ⊢
  exact hd

/-- All Sylow subgroups away from two and three are cyclic. -/
theorem sylow_isCyclic_of_ne_two_ne_three {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (P : Sylow p (OddPrime.Sp (ZMod 3))) :
    IsCyclic P := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact isCyclic_of_card_dvd_prime (p := 5)
    (sylow_card_dvd_five_of_ne_two_ne_three hp2 hp3 P)

/-- Transfer excludes every prime except two and three from a finite perfect
central kernel over the actual Sp₄(3). -/
theorem not_dvd_card_kernel_of_ne_two_ne_three
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (OddPrime.Sp (ZMod 3)))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_card_multiplier_of_isCyclic_sylow (sylow_isCyclic_of_ne_two_ne_three hp2 hp3)

/-- The two remaining prime branches in the ternary section construction. -/
theorem prime_dvd_kernel_eq_two_or_three
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (OddPrime.Sp (ZMod 3)))
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card f.toMonoidHom.ker) :
    p = 2 ∨ p = 3 := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases h2 : p = 2
  · exact Or.inl h2
  by_cases h3 : p = 3
  · exact Or.inr h3
  exact (not_dvd_card_kernel_of_ne_two_ne_three f h2 h3 hd).elim

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection
