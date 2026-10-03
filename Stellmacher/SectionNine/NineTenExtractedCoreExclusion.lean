module

public import Stellmacher.SectionNine.LemmaNineThree
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Stellmacher.SectionNine.NineTenExtraction

/-!
# The extracted center escapes the first-step core in (9.10)

Assume the first-step center does not lie in the terminal neighbor module.
Every terminal neighbor center acting nontrivially on the first-step module
then escapes the first-step core. Indeed, (9.3) and its next-module consequence
identify the commutator with that core as the order-two first-step center.
A nontrivial commutator inside this line would equal the line. But the terminal
module is normalized by the first-step module, so that commutator also lies
in the terminal module, a contradiction.

This proves the core exclusion in the first paragraph of (9.10) from the
explicit center noncontainment obtained there via (9.9). It does not assume
or invoke the unfinished numbered distance bounds. Source: Stellmacher,
Journal of Algebra 190 (1997), printed p.57 / PDF p.47.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

private theorem extracted_center_not_le_first_core_of_four
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcomm : ⁅ZAt ctx.Γ neighbor, VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥) :
    ¬ ZAt ctx.Γ neighbor ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let comm := ⁅ZAt Γ neighbor, VAt Γ cp.firstStep⁆
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hnormalize : VAt Γ cp.firstStep ≤ Subgroup.normalizer (VAt Γ cp.a' : Set G) :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2.trans
      (stabilizer_le_normalizer_v Γ cp.a')
  have hcommV : comm ≤ VAt Γ cp.a' :=
    (Subgroup.commutator_mono hneighborV le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalize)
  intro hcore
  have hcommCenter : comm ≤ ZAt Γ cp.firstStep := by
    rw [← nine_next_module_commutator_of_initial_four ctx hfour]
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono hcore le_rfl
  have hcommCenterEq : comm = ZAt Γ cp.firstStep := by
    apply Subgroup.eq_of_le_of_card_ge hcommCenter
    rw [nine_next_center_order_of_initial_four ctx hfour]
    exact (Subgroup.one_lt_card_iff_ne_bot comm).mpr hcomm
  exact hnot (hcommCenterEq ▸ hcommV)

public theorem nine_ten_extracted_center_not_le_first_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcomm : ⁅ZAt ctx.Γ neighbor, VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥) :
    ¬ ZAt ctx.Γ neighbor ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  have hfour := (lemma_nine_three_ambient ctx hb ctx.criticalPath.a
    ⟨1, ctx.Γ.act_one _⟩).2
  exact extracted_center_not_le_first_core_of_four ctx.toLocalContext
    hfour hnot neighbor hneighbor hcomm

end Stellmacher.SectionNine
