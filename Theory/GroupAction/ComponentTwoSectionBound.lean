module
public import Theory.GroupAction.ComponentSmallTwoSection

/-!
# The first two-section on which a component divisible by seventeen can act

The powers of two below 256 have distinct residues modulo seventeen.
A seventeen-subgroup of automorphisms of such a two-group therefore fixes
every element. Consequently a two-perfect actor with a simple quotient
divisible by seventeen centralizes every normalized two-section of order
less than 256. This includes nonabelian sections and retains their full kernel.

This sharpens the small-section calculation used in MS93 (5.7), p.919.
Its original amalgam application is in Sp4Four.DistanceReduction.RadiusObstruction.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement

theorem MulAut.not_seventeen_dvd_card_of_twoGroup_card_lt_256
    {V : Type*} [Group V] [Finite V] (hV : IsPGroup 2 V) (hcard : Nat.card V < 256) :
    ¬ 17 ∣ Nat.card (MulAut V) := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  intro hdiv
  obtain ⟨n,hn⟩ := hV.exists_card_eq
  have hnle : n ≤ 7 := by
    have : 2^n < 2^8 := by simpa only [←hn, show (2:ℕ)^8=256 from rfl] using hcard
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp this
    omega
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

theorem commutator_component_le_of_seventeen_section_lt_256
    {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]
    (L D Z : Subgroup G) [Finite L] [Finite D] [(Z.subgroupOf D).Normal]
    (hL : IsPPerfect 2 L) (q : L →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (hD : IsPGroup 2 D) (hcard : Z.relIndex D < 256)
    (hLD : L ≤ normalizer (D : Set G)) (hLZ : L ≤ normalizer (Z : Set G)) :
    ⁅D,L⁆ ≤ Z := by
  let V := D ⧸ Z.subgroupOf D
  have hV : IsPGroup 2 V := hD.to_quotient _
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action L D Z hLD hLZ inferInstance
  have him : IsPGroup 2 a.range := MonoidHom.isPGroup_range_of_simple_quotient q hq hker
    a 17 hS (MulAut.not_seventeen_dvd_card_of_twoGroup_card_lt_256 hV hcard)
  have hk := pResidual_le_ker_of_isPGroup 2 a.rangeRestrict him
  rw [MonoidHom.ker_rangeRestrict,(pResidual_eq_top_iff 2 L).mpr hL] at hk
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl d hd
  have htriv : a ⟨l,hl⟩ = 1 := hk (mem_top _)
  have hfix := ha ⟨l,hl⟩ ⟨d,hd⟩
  rw [htriv] at hfix
  have hmember := QuotientGroup.eq_iff_div_mem.mp hfix.symm
  change l*d*l⁻¹/d ∈ Z at hmember
  simpa only [div_eq_mul_inv,commutatorElement_def] using hmember
end Subgroup
