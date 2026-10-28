module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Overgroups

/-!
# Prime support of the original diagonal centralizer

The vanishing full fixed part makes C_{L₀T}(ab) a proper subgroup of L₀T.
It contains the original Sylow subgroup T, so the proved linear-three
proper-overgroup calculation restricts its prime support to two and three.
The literal subgroup C_{L₀}(ab) inherits that restriction.

Source: Aschbacher--Smith 10.1.1(3), 10.2.3(ii), and 10.2.11,
printed pp.741,745,753. No centralizer-core bound is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Local
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- The prime-spectrum field on the original centralizer. -/
theorem prime_spectrum (c : Configuration s a b) :
    IsPiGroup twoThreePrimes
    (localOrbit T L ⊓ centralizer ({a*b} : Set G) : Subgroup G) := by
  let K : Subgroup G := localOrbit T L ⊓ centralizer ({a*b} : Set G)
  let P : Subgroup G := localJoin T L ⊓ centralizer ({a*b} : Set G)
  have hKP : K ≤ P := inf_le_inf_right _ le_sup_left
  have hTP : (T : Subgroup G) ≤ P := le_inf le_sup_right c.sylow_le
  have hlt : P < localJoin T L := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hz : a*b ∈ D.fullModule := D.fullModule.mul_mem
      (survivor_moved_le s c.first_mem) (survivor_partner_le s c.second_mem)
    have hJC : localJoin T L ≤ centralizer ({a*b} : Set G) := he ▸ inf_le_right
    have hfixed : a*b ∈ centralizer (localOrbit T L : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hJC (mem_sup_left hx))
    have hzero : a*b = 1 := mem_bot.mp (c.fixed ▸ (show
      a*b ∈ D.fullModule ⊓ centralizer (localOrbit T L : Set G) from ⟨hz,hfixed⟩))
    have ho := c.order
    rw [hzero, orderOf_one] at ho
    omega
  have h6 : IsPGroup 6 K :=
    (CentralHall.LinearThree.source_proper_overgroup_six D s.quotient
      (survivor_nonnormal s) P hTP hlt).to_le hKP
  rw [IsPiGroup_iff twoThreePrimes]
  intro p hp
  obtain ⟨n, hn⟩ := h6.exists_card_dvd_pow
  have hpd : p.val ∣ 6 := by
    apply p.property.dvd_of_dvd_pow
    exact hp.trans hn
  have hpd' : p.val = 2 ∨ p.val = 3 := by
    have := p.property.dvd_mul.mp (show p.val ∣ 2*3 from hpd)
    rcases this with h | h
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left p.property.ne_one)
  exact hpd'
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Local
