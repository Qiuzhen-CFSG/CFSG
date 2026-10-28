module
public import Theory.GroupAction.SimpleSeventeenSmallSection
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Small sections normalized by a two-perfect simple cover

A two-perfect actor with a simple quotient divisible by seventeen acts
trivially on any normalized two-section of order at most sixty-four.
The quotient may have a fixed central attachment; neither the subgroup
nor its denominator must be normalized by a larger ambient group.
The proof uses the literal conjugation action and the absence of a
seventeen-element in the automorphism group of the small section.
Source application: MS93 (5.7), printed p.919.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup

/-- The given two-perfect actor fixes the literal small quotient. -/
theorem commutator_le_of_twoPerfect_simple_seventeen_small_section
    {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]
    (A H Z : Subgroup G) [Finite A] [Finite H]
    (hA : IsPPerfect 2 A)
    (q : A →* S) (hq : Function.Surjective q) (hker : IsPGroup 2 q.ker)
    (hS : 17 ∣ Nat.card S) (hH : IsPGroup 2 H)
    (hAH : A ≤ normalizer (H : Set G)) (hAZ : A ≤ normalizer (Z : Set G))
    (hN : (Z.subgroupOf H).Normal) (hi : Z.relIndex H ≤ 64) :
    ⁅H,A⁆ ≤ Z := by
  let := hN
  let W := H ⧸ Z.subgroupOf H
  have hW : IsPGroup 2 W := hH.to_quotient _
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action A H Z hAH hAZ hN
  have hp : IsPGroup 2 ρ.range := MonoidHom.isPGroup_range_of_simple_quotient
    q hq hker ρ 17 hS (MulAut.not_seventeen_dvd_card_of_twoGroup_card_le_sixtyFour hW hi)
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
