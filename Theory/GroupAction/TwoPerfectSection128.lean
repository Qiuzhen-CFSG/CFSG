module
public import Theory.GroupAction.TwoPerfectSmallSection
/-!
# Two-perfect actions on two-sections of order at most 128

The powers of two through 128 have distinct residues modulo seventeen.
An order-seventeen automorphism therefore fixes the entire two-group.
A two-perfect cover of a simple group with order divisible by seventeen
then acts trivially on every normalized two-section of this size.

This includes the possible order-two common edge center in the original
paired-seed argument of MS93 (5.7), p.919. Its actual consumer is
GenerationTwoSymplecticPairedSelection.
-/

public section
open Subgroup
open scoped commutatorElement
/-- Automorphisms of a two-group of order at most 128 have order prime to 17. -/
theorem MulAut.not_seventeen_dvd_card_of_twoGroup_card_le_oneTwentyEight
    {V : Type*} [Group V] [Finite V] (hV : IsPGroup 2 V) (hcard : Nat.card V ≤ 128) :
    ¬ 17 ∣ Nat.card (MulAut V) := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  intro hdiv
  obtain ⟨n,hn⟩ := hV.exists_card_eq
  have hnle : n ≤ 7 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hcard
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 17 hdiv
  let P := zpowers a
  have hP : Nat.card P = 17 := by rw [Nat.card_zpowers,ha]
  have hp : IsPGroup 17 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  let F := FixedPoints.subgroup P V
  have hmod := hp.card_modEq_card_fixedPoints V
  change Nat.card V % 17 = Nat.card F % 17 at hmod
  have hFdiv : Nat.card F ∣ 2^n := hn ▸ F.card_subgroup_dvd_card
  obtain ⟨k,hk,hFcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdiv
  have heq : Nat.card F = Nat.card V := by
    rw [hn,hFcard] at hmod ⊢
    interval_cases n <;> interval_cases k <;> norm_num at *
  have htop := F.eq_top_of_card_eq heq
  have haone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ F from htop ▸ mem_top x) ⟨a,mem_zpowers a⟩
  rw [haone,orderOf_one] at ha
  norm_num at ha


namespace Subgroup
/-- The given two-perfect actor fixes the literal small quotient. -/
theorem commutator_le_of_twoPerfect_simple_seventeen_section_le_128
    {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]
    (A H Z : Subgroup G) [Finite A] [Finite H]
    (hA : IsPPerfect 2 A)
    (q : A →* S) (hq : Function.Surjective q) (hker : IsPGroup 2 q.ker)
    (hS : 17 ∣ Nat.card S) (hH : IsPGroup 2 H)
    (hAH : A ≤ normalizer (H : Set G)) (hAZ : A ≤ normalizer (Z : Set G))
    (hN : (Z.subgroupOf H).Normal) (hi : Z.relIndex H ≤ 128) :
    ⁅H,A⁆ ≤ Z := by
  let := hN
  let W := H ⧸ Z.subgroupOf H
  have hW : IsPGroup 2 W := hH.to_quotient _
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action A H Z hAH hAZ hN
  have hp : IsPGroup 2 ρ.range := MonoidHom.isPGroup_range_of_simple_quotient
    q hq hker ρ 17 hS (MulAut.not_seventeen_dvd_card_of_twoGroup_card_le_oneTwentyEight hW hi)
  have hk := pResidual_le_ker_of_isPGroup 2 ρ.rangeRestrict hp
  rw [MonoidHom.ker_rangeRestrict, (pResidual_eq_top_iff 2 A).mpr hA] at hk
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha h hh
  have hz : ρ ⟨a,ha⟩ = 1 := hk (mem_top _)
  have he := hρ ⟨a,ha⟩ ⟨h,hh⟩
  rw [hz] at he
  have hm := QuotientGroup.eq_iff_div_mem.mp he.symm
  change a*h*a⁻¹/h ∈ Z at hm
  simpa only [div_eq_mul_inv,commutatorElement_def] using hm

end Subgroup
