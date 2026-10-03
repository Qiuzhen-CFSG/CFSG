module
public import Stellmacher.SectionNine.NineEightInitialExtraction
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Stellmacher.SectionNine.NineSevenNormalityObstructions
public import Stellmacher.SectionNine.NineNineCommutatorBound
public import Stellmacher.SectionEight.EightFourSourceNineCommutingCore


/-!
# Commutator bounds in the contained-center branch of Stellmacher (9.8)

Assume the terminal center lies in the first-step module and take the actual
neighbor extracted by the index-two W argument. If that neighbor's center
lies in the initial stabilizer, its nontrivial commutator with the initial
center is exactly the first-step center. Its commutator with the entire
initial neighborhood subgroup lies in the join of the first-step and
terminal center lines.

Both center planes have order four by (9.3). Normalization of an index-two
line bounds the center commutator, and bounds the commutator of the
index-two stabilizer intersection by the terminal line. The initial center
escapes that intersection, so their join is the whole neighborhood group.
The group is abelian because the critical distance is at least five, hence
it normalizes the joined target and the two bounds combine.

Source: Stellmacher (9.8), first contained-center branch, printed p.55/PDF
p.45 of `refs/files/stellmacher-n-group.pdf`.
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

public theorem nine_eight_contained_center_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcontained : ZAt ctx.Γ neighbor ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hnoncomm : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).2
  have htwo := nine_next_center_order_of_initial_four ctx.toLocalContext hfour
  have hline := ((nine_seven_center_join ctx cp.a ⟨1, Γ.act_one _⟩).2
    cp.firstStep ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2
  have hindex := relIndex_two_of_cards _ _ hline htwo hfour
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hneighborFirst := hneighborV.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hcommLe := Stellmacher.SectionEight.commutator_le_of_normalizing_index_two
    (ZAt Γ cp.a) (ZAt Γ cp.firstStep) (ZAt Γ neighbor) hindex
    (hcontained.trans (stabilizer_le_normalizer_z Γ cp.a))
    (hneighborFirst.trans (stabilizer_le_normalizer_z Γ cp.firstStep))
  apply Subgroup.eq_of_le_of_card_ge hcommLe
  change Nat.card (ZAt Γ cp.firstStep) = 2 at htwo
  rw [htwo]
  exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hnoncomm

public theorem nine_eight_contained_center_neighborhood_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcontained : ZAt ctx.Γ neighbor ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hindex : QuotientCardEq (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
      (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ neighbor) 2)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor)
    (hnoncomm : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥) :
    ⁅GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ ZAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W := GeneratedNeighborhoodV Γ cp.a
  let I := W ⊓ GAt Γ neighbor
  let target := ZAt Γ cp.firstStep ⊔ ZAt Γ cp.a'
  have hlong : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hcomm := nine_eight_contained_center_commutator ctx hlong neighbor hneighbor hcontained hnoncomm
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
  have hIindex : I.relIndex W = 2 := by
    have hmul := (I.subgroupOf W).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show I ≤ W from inf_le_left)).toEquiv]
      at hmul
    change I.relIndex W * Nat.card I = Nat.card W at hmul
    change Nat.card W = 2 * Nat.card I at hindex
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hmul.trans hindex)
  have hjoin : ZAt Γ cp.a ⊔ I = W := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hZW inf_le_left)
    have hproper : ¬ ZAt Γ cp.a ⊔ I ≤ I := by
      intro hle
      exact hnot (le_sup_left.trans (hle.trans inf_le_right))
    have hindexJoin : I.relIndex (ZAt Γ cp.a ⊔ I) = 2 := by
      have hdvd : I.relIndex (ZAt Γ cp.a ⊔ I) ∣ I.relIndex W :=
        ⟨(ZAt Γ cp.a ⊔ I).relIndex W,
          (Subgroup.relIndex_mul_relIndex I (ZAt Γ cp.a ⊔ I) W le_sup_right
            (sup_le hZW inf_le_left)).symm⟩
      rw [hIindex] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
      · exact (hproper (Subgroup.relIndex_eq_one.mp hone)).elim
      · exact htwo
    have hmul := (I.subgroupOf (ZAt Γ cp.a ⊔ I)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show I ≤ ZAt Γ cp.a ⊔ I from le_sup_right)).toEquiv] at hmul
    change I.relIndex (ZAt Γ cp.a ⊔ I) * Nat.card I = Nat.card (ZAt Γ cp.a ⊔ I : Subgroup G) at hmul
    rw [hindexJoin] at hmul
    change Nat.card W = 2 * Nat.card I at hindex
    exact (hindex.trans hmul).le
  have hWcomm : IsMulCommutative W := nine_eight_neighborhood_abelian ctx.toLocalContext
    (by have hge := nine_ten_length_ge_five ctx.toLocalContext hb; change 5 ≤ cp.length at hge; change 4 < cp.length; omega) cp.a
  have htargetW : target ≤ W := sup_le
    (((nine_seven_center_join ctx cp.a ⟨1, Γ.act_one _⟩).2 cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2.trans hZW)
    (hcontain.trans (nine_eight_v_le_generated_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)))
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
      exact ⟨hZW, hcomm.le.trans le_sup_left⟩
    · apply (le_nineNineCommutatorBound_iff _ _ _ _ _).mpr
      exact ⟨inf_le_left, hIcomm.trans le_sup_right⟩
  exact (hbound helement).2 mover hmover

end Stellmacher.SectionNine
