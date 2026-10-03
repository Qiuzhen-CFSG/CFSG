module

public import Stellmacher.SectionNine.LemmaNineThree
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Stellmacher.SectionNine.NineSevenCenterJoin
public import Stellmacher.SectionEight.EightFourSourceNineCommutingCore

/-!
# The initial center centralizes the terminal coatom

The terminal-module intersection with the initial stabilizer normalizes
both the initial center and its first-step center line. By (9.3) their
orders are four and two, so the commutator lies in the line. The critical
initial center normalizes the terminal module by (7.4), placing that same
commutator inside terminal V. The source assumption that the first-step
center is not contained in terminal V forces the commutator to be trivial.

This applies to the coatom of the actual normalized second extraction
without identifying its extracted group with a smaller generated-center
subgroup. Source: Stellmacher (9.10), printed p.57, the sentence preceding
assertion (2), `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_initial_center_centralizes_terminal_coatom
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ⁅ZAt ctx.Γ ctx.criticalPath.a,
      VAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let actors := VAt Γ cp.a' ⊓ GAt Γ cp.a
  let comm := ⁅ZAt Γ cp.a, actors⁆
  have hinitialCard := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).2
  have hfirstCard := nine_next_center_order_of_initial_four ctx.toLocalContext hinitialCard
  change Nat.card (ZAt Γ cp.a) = 4 at hinitialCard
  change Nat.card (ZAt Γ cp.firstStep) = 2 at hfirstCard
  have hfirstNeighbor : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hline : ZAt Γ cp.firstStep ≤ ZAt Γ cp.a :=
    ((nine_seven_center_join ctx cp.a ⟨1, Γ.act_one _⟩).2 cp.firstStep
      hfirstNeighbor).2
  have hindex : (ZAt Γ cp.firstStep).relIndex (ZAt Γ cp.a) = 2 := by
    have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hline).toEquiv
    have hproduct := ((ZAt Γ cp.firstStep).subgroupOf (ZAt Γ cp.a)).index_mul_card
    rw [hcard, hfirstCard, hinitialCard] at hproduct
    change ((ZAt Γ cp.firstStep).subgroupOf (ZAt Γ cp.a)).index = 2
    omega
  have hcommLine : comm ≤ ZAt Γ cp.firstStep := by
    apply Stellmacher.SectionEight.commutator_le_of_normalizing_index_two _ _ _ hindex
    · exact inf_le_right.trans (stabilizer_le_normalizer_z Γ cp.a)
    · exact (inf_le_left.trans
        (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2).trans
        (stabilizer_le_normalizer_z Γ cp.firstStep)
  have hcontain := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment
  have hnormal : ZAt Γ cp.a ≤ Subgroup.normalizer (VAt Γ cp.a' : Set G) :=
    (hcontain.1.trans hcontain.2).trans (stabilizer_le_normalizer_v Γ cp.a')
  have hcommTerminal : comm ≤ VAt Γ cp.a' := by
    rw [show comm = ⁅actors, ZAt Γ cp.a⁆ from Subgroup.commutator_comm _ _]
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal)
  by_contra hnonzero
  have heq : comm = ZAt Γ cp.firstStep := by
    apply Subgroup.eq_of_le_of_card_ge hcommLine
    rw [hfirstCard]
    exact (Subgroup.one_lt_card_iff_ne_bot comm).mpr hnonzero
  exact hnot (heq ▸ hcommTerminal)

end Stellmacher.SectionNine
