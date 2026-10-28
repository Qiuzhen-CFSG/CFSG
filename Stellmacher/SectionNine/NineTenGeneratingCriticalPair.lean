module

public import Stellmacher.SectionNine.NineTenExtractedCoreExclusion
public import Stellmacher.SectionNine.NineSevenCenterJoin
public import Stellmacher.SectionNine.NineThreeReplacementCriticalPair
public import Stellmacher.SectionEight.EightFourSourceNineCommutingCore

/-!
# Generating neighbors give critical pairs in (9.10)

Suppose the terminal center escapes the first-step neighbor module. At any
terminal neighbor, the terminal center is an index-two subgroup of its
order-four center. The intersection of the first-step module with the
neighbor stabilizer normalizes both. Its commutator is therefore contained
in the terminal center, but also in the first-step module, and must vanish.
This intermediate result is public for the later same-witness support-actor
selection.

If the center of this terminal neighbor generates the first-step stabilizer
with the edge at another neighbor, those two neighbor centers cannot commute:
otherwise both generators normalize the second center, violating the common
neighbor-center normalizer obstruction. The second center therefore escapes
the first neighbor stabilizer and hence the terminal core. Critical minimality
and the already-proved replacement lemma give criticality, center commutation,
and the distance identity needed for prescribed-neighbor normalization.

Source: Stellmacher (9.10)(1), Journal of Algebra 190 (1997), printed p.57.
The source's pending (9.8) consequence is an explicit noncontainment hypothesis.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

private theorem terminal_neighbor_initial_orbit
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a') :
    IsConjugateVertex ctx.Γ ctx.criticalPath.a neighbor := by
  obtain ⟨alignment, halign, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hpen := (nine_three_initial_extraction_inputs ctx hb).1
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    ctx.criticalPath.a' hpen hneighbor
  refine ⟨alignment * (actor : G), ?_⟩
  rw [ctx.Γ.act_mul, halign]
  exact hactor

public theorem nine_ten_terminal_neighbor_center_centralizes_first_coatom
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a') :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ neighbor,
      ZAt ctx.Γ neighbor⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let actors := VAt Γ cp.firstStep ⊓ GAt Γ neighbor
  let comm := ⁅actors, ZAt Γ neighbor⁆
  have horbit := terminal_neighbor_initial_orbit ctx.toLocalContext hb neighbor hneighbor
  have hneighborCard := (lemma_nine_three_ambient ctx hb neighbor horbit).2
  have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).2
  obtain ⟨alignment, _, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hterminalCard := (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext
    hfour cp.a' ⟨alignment, hterminal⟩).1
  change Nat.card (ZAt Γ cp.a') = 2 at hterminalCard
  change Nat.card (ZAt Γ neighbor) = 4 at hneighborCard
  have hreverse : cp.a' ∈ neighborhood Γ neighbor :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))
  have hline : ZAt Γ cp.a' ≤ ZAt Γ neighbor :=
    ((nine_seven_center_join ctx neighbor horbit).2 cp.a' hreverse).2
  have hindex : (ZAt Γ cp.a').relIndex (ZAt Γ neighbor) = 2 := by
    have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hline).toEquiv
    have hproduct := ((ZAt Γ cp.a').subgroupOf (ZAt Γ neighbor)).index_mul_card
    rw [hcard, hterminalCard, hneighborCard] at hproduct
    change ((ZAt Γ cp.a').subgroupOf (ZAt Γ neighbor)).index = 2
    omega
  have hcommLine : comm ≤ ZAt Γ cp.a' := by
    rw [show comm = ⁅ZAt Γ neighbor, actors⁆ from Subgroup.commutator_comm _ _]
    apply Stellmacher.SectionEight.commutator_le_of_normalizing_index_two _ _ _ hindex
    · exact inf_le_right.trans (stabilizer_le_normalizer_z Γ neighbor)
    · exact (inf_le_left.trans
        (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2).trans
        (stabilizer_le_normalizer_z Γ cp.a')
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hnormal : ZAt Γ neighbor ≤ Subgroup.normalizer (VAt Γ cp.firstStep : Set G) :=
    (hneighborV.trans (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2).trans
      (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hcommFirst : comm ≤ VAt Γ cp.firstStep :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal)
  by_contra hnonzero
  have heq : comm = ZAt Γ cp.a' := by
    apply Subgroup.eq_of_le_of_card_ge hcommLine
    rw [hterminalCard]
    exact (Subgroup.one_lt_card_iff_ne_bot comm).mpr hnonzero
  exact hnot (heq ▸ hcommFirst)

public theorem nine_ten_generating_neighbor_critical_pair
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (terminalNeighbor firstNeighbor : ctx.Γ.Vertex)
    (hterminal : terminalNeighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hfirst : firstNeighbor ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ firstNeighbor) ⊔
      ZAt ctx.Γ terminalNeighbor = GAt ctx.Γ ctx.criticalPath.firstStep) :
    IsCriticalPair ctx.Γ firstNeighbor ctx.criticalPath.a' ∧
      ⁅ZAt ctx.Γ firstNeighbor, ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ ∧
      ctx.Γ.distance firstNeighbor ctx.criticalPath.a' =
        ctx.Γ.distance ctx.criticalPath.firstStep ctx.criticalPath.a' + 1 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hnoncomm : ⁅ZAt Γ firstNeighbor, ZAt Γ terminalNeighbor⁆ ≠ ⊥ := by
    intro hbot
    apply neighbor_center_not_normalized ctx.sectionSeven Γ cp.firstStep firstNeighbor hfirst
    change GAt Γ cp.firstStep ≤ Subgroup.normalizer (ZAt Γ firstNeighbor : Set G)
    rw [← hgenerate]
    rw [Subgroup.commutator_comm] at hbot
    exact sup_le
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ firstNeighbor))
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot).trans
        (Subgroup.centralizer_le_normalizer _))
  have hfirstV : ZAt Γ firstNeighbor ≤ VAt Γ cp.firstStep := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨firstNeighbor, hfirst, rfl⟩
  have houtside : ¬ ZAt Γ firstNeighbor ≤ GAt Γ terminalNeighbor := by
    intro hle
    apply hnoncomm
    exact bot_unique ((Subgroup.commutator_mono (le_inf hfirstV hle) le_rfl).trans_eq
      (nine_ten_terminal_neighbor_center_centralizes_first_coatom ctx hb hnot terminalNeighbor hterminal))
  have hnotCore : ¬ ZAt Γ firstNeighbor ≤ QAt Γ cp.a' := by
    intro hle
    exact houtside (hle.trans
      ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a' terminalNeighbor
        hterminal default).2.2)
  exact nine_three_replacement_initial_critical_pair ctx.toLocalContext hb
    firstNeighbor hfirst hnotCore

end Stellmacher.SectionNine
