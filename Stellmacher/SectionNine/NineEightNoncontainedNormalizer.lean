module
public import Stellmacher.SectionNine.NineEightContainedCenterCommutators
public import Stellmacher.SectionNine.NineFiveConjugatorAlgebra

/-!
# The proper normalizer join in the second branch of Stellmacher (9.8)

For a terminal neighbor extracted under the original (9.8) hypotheses,
its center commutator with the initial neighborhood subgroup W lies in
the first-step module. Therefore the join of that center with the initial
edge stabilizer normalizes W, and is proper in the first-step stabilizer.
This remains true without assuming the center escapes the initial stabilizer;
that escape will make the join strictly larger than the edge in the next step.

The extracted index-two intersection and the escaping initial center
generate W. The intersection's commutator lies in the terminal center
by the index-two line in the terminal neighbor's center plane. The initial
center's commutator lies in the first-step module by normalization.
Abelianness of W combines these bounds. Equality of the resulting join
with the first-step stabilizer would make W normalized by adjacent vertex
stabilizers, contradicting the proved normality obstruction.

Source: Stellmacher (9.8), printed p.55/PDF p.45, the displayed commutator
bound and the proper generated subgroup before assertion (*).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u

private theorem relIndex_two_of_cards
    {G : Type u} [Group G] [Finite G] (small large : Subgroup G)
    (hle : small ≤ large) (hsmall : Nat.card small = 2) (hlarge : Nat.card large = 4) :
    small.relIndex large = 2 := by
  have hmul := (small.subgroupOf large).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hsmall, hlarge] at hmul
  change (small.subgroupOf large).index = 2
  omega

public theorem nine_eight_extracted_center_neighborhood_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
      (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ neighbor) 2)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor) :
    ⁅GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W := GeneratedNeighborhoodV Γ cp.a
  let I := W ⊓ GAt Γ neighbor
  let target := VAt Γ cp.firstStep
  have hlong : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hfour := (lemma_nine_three_ambient ctx hlong cp.a ⟨1, Γ.act_one _⟩).2
  obtain ⟨alignment, halign, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpen := (nine_three_initial_extraction_inputs ctx.toLocalContext hlong).1
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    cp.a' hpen hneighbor
  have horbit : IsConjugateVertex Γ cp.a neighbor := by
    refine ⟨alignment * (actor : G), ?_⟩
    rw [Γ.act_mul, halign]
    exact hactor
  have hneighborCard := (lemma_nine_three_ambient ctx hlong neighbor horbit).2
  have hterminalCard := (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext
    hfour cp.a' ⟨alignment, hterminal⟩).1
  have hreverse : cp.a' ∈ neighborhood Γ neighbor :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))
  have hline := ((nine_seven_center_join ctx neighbor horbit).2 cp.a' hreverse).2
  have hlineIndex := relIndex_two_of_cards _ _ hline hterminalCard hneighborCard
  have hWterminal : W ≤ GAt Γ cp.a' := nine_eight_neighborhood_le_terminal ctx hb hcontain cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
  have hIcomm : ⁅I, ZAt Γ neighbor⁆ ≤ ZAt Γ cp.a' := by
    rw [Subgroup.commutator_comm]
    exact Stellmacher.SectionEight.commutator_le_of_normalizing_index_two _ _ _ hlineIndex
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ neighbor))
      ((inf_le_left.trans hWterminal).trans (stabilizer_le_normalizer_z Γ cp.a'))
  have hZW : ZAt Γ cp.a ≤ W :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1.trans
      (nine_eight_v_le_generated_neighborhood Γ
        ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj))
  have hjoin : ZAt Γ cp.a ⊔ I = W := by
    apply le_antisymm (sup_le hZW inf_le_left)
    obtain ⟨element, helement, houtside⟩ := SetLike.not_le_iff_exists.mp hnot
    exact nine_five_index_two_span_of_element I W _ inf_le_left hindex le_sup_right
      element (hZW helement) (fun h => houtside h.2) ((show ZAt Γ cp.a ≤ ZAt Γ cp.a ⊔ I from le_sup_left) helement)
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hneighborFirst := hneighborV.trans (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hcomm : ⁅ZAt Γ cp.a, ZAt Γ neighbor⁆ ≤ target :=
    (Subgroup.commutator_mono (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hneighborFirst.trans (stabilizer_le_normalizer_v Γ cp.firstStep)))
  have hWcomm : IsMulCommutative W := nine_eight_neighborhood_abelian ctx.toLocalContext
    (by have hge := nine_ten_length_ge_five ctx.toLocalContext hb; change 5 ≤ cp.length at hge; change 4 < cp.length; omega) cp.a
  have htargetW : target ≤ W := nine_eight_v_le_generated_neighborhood Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
  have hnormal : W ≤ Subgroup.normalizer (target : Set G) :=
    ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hWcomm).trans
      (Subgroup.centralizer_le htargetW)).trans (Subgroup.centralizer_le_normalizer _)
  change ⁅W, ZAt Γ neighbor⁆ ≤ target
  rw [← hjoin]
  apply Subgroup.commutator_le.mpr
  intro element helement mover hmover
  have hbound : ZAt Γ cp.a ⊔ I ≤
      nineNineCommutatorBound W (ZAt Γ neighbor) target hnormal := by
    apply sup_le
    · apply (le_nineNineCommutatorBound_iff _ _ _ _ _).mpr
      exact ⟨hZW, hcomm⟩
    · apply (le_nineNineCommutatorBound_iff _ _ _ _ _).mpr
      exact ⟨inf_le_left, hIcomm.trans hcontain⟩
  exact (hbound helement).2 mover hmover

public theorem nine_eight_extracted_center_proper_join
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
      (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ neighbor) 2)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor) :
    (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) ⊔
      ZAt ctx.Γ neighbor < GAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W := GeneratedNeighborhoodV Γ cp.a
  let J := (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) ⊔ ZAt Γ neighbor
  have hcomm := nine_eight_extracted_center_neighborhood_commutator ctx hb hcontain
    neighbor hneighbor hindex hnot
  have hfirstW : VAt Γ cp.firstStep ≤ W := nine_eight_v_le_generated_neighborhood Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
  have hnormal : J ≤ Subgroup.normalizer (W : Set G) := sup_le
    (inf_le_left.trans (nine_seven_stabilizer_normalizes_neighborhood Γ cp.a))
    (Subgroup.le_normalizer_iff_commutator_le_left.mpr (hcomm.trans hfirstW))
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor,hneighbor,rfl⟩
  have hJP : J ≤ GAt Γ cp.firstStep := sup_le inf_le_right
    (hneighborV.trans (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2)
  apply lt_of_le_of_ne hJP
  intro heq
  have hlong : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hZW : ZAt Γ cp.a ≤ W :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1.trans hfirstW
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hZbot := le_bot_iff.mp (hbot ▸ hZW)
    have hfour := (lemma_nine_three_ambient ctx hlong cp.a ⟨1, Γ.act_one _⟩).2
    rw [hZbot,Subgroup.card_bot] at hfour
    omega
  apply nine_seven_neighborhood_not_normalized_by_neighbor ctx.toLocalContext
    (by change 3 < cp.length at hb; change 2 < cp.length; omega) cp.firstStep_adj hWne
  exact heq ▸ hnormal

end Stellmacher.SectionNine
