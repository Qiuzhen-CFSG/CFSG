module

public import Theory.GroupAction.SimpleSeventeenSmallSection
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# A component centralizes small normalized two-sections

A finite two-perfect actor with simple quotient divisible by17 has no
nontrivial action on a normalized two-section of order at most64. Its image
in the section automorphism group avoids17, hence is a two-group; two-
perfectness kills that image. The section need not be contained in the
actor, and the entire ambient quotient need not be simple.

This supplies the small-section choice in MS93 (2.1)(vii),(3.4), before
outer automorphisms of the local component have been removed. Literal
subgroup quotients retain every central attachment.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]

theorem commutator_component_le_of_seventeen_small_section
    (L D Z : Subgroup G) [Finite L] [Finite D] [(Z.subgroupOf D).Normal]
    (hL : IsPPerfect 2 L) (q : L →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (hD : IsPGroup 2 D) (hcard : Z.relIndex D ≤ 64)
    (hLD : L ≤ normalizer (D : Set G)) (hLZ : L ≤ normalizer (Z : Set G)) :
    ⁅D,L⁆ ≤ Z := by
  let V := D ⧸ Z.subgroupOf D
  have hV : IsPGroup 2 V := hD.to_quotient _
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action L D Z hLD hLZ inferInstance
  have him : IsPGroup 2 a.range := MonoidHom.isPGroup_range_of_simple_quotient q hq hker
    a 17 hS (MulAut.not_seventeen_dvd_card_of_twoGroup_card_le_sixtyFour hV hcard)
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
