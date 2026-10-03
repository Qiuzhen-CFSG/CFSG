module
public import Stellmacher.SectionNine.NineEightContainedCenterCommutators
public import Stellmacher.SectionNine.NineNineMaximalIntersection
public import Theory.GroupTheory.Commutator.BoundedImageKernel
public import Theory.GroupTheory.NormalizedSupCard


/-!
# The backward index in the contained-center branch of Stellmacher (9.8)

Under the original (9.8) terminal-center containment, suppose the extracted
neighbor center lies in the initial stabilizer. For every neighbor preceding
the initial vertex and distinct from the first step, its V-module intersects
the first-step module with index exactly two.

The proved commutator bounds put the neighborhood commutator in the join
of two center lines. The terminal line centralizes the abelian neighborhood
group and has index two in the acting center plane. A commutator kernel
modulo the first-step line therefore has index at most two in the preceding
module. The maximal commutator-bound transport puts it in the first-step
module. Equality of distinct neighboring modules is impossible: cubic
two-arc transitivity would make all those modules equal, and the initial
stabilizer would normalize one of them, violating the edge normality
obstruction. Thus the index is exactly two.

This proves the first-branch index calculation preceding the application
of (9.7) in Stellmacher (9.8), printed p.55/PDF p.45 of
`refs/files/stellmacher-n-group.pdf`. It does not assume (9.7).
The distinct-neighbor-module step is also public for the index-one exclusion
in (9.9); it uses the same cubic two-arc transport and normalization obstruction.

-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u

public theorem nine_eight_contained_center_backward_bound
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
    (hnoncomm : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep) :
    Nat.card (VAt ctx.Γ previous) ≤
      2 * Nat.card (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W := GeneratedNeighborhoodV Γ cp.a
  let Vprev := VAt Γ previous
  let Zfirst := ZAt Γ cp.firstStep
  let Zterminal := ZAt Γ cp.a'
  let Zneighbor := ZAt Γ neighbor
  let R := Zfirst ⊔ Zterminal
  have hlong : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hfour := (lemma_nine_three_ambient ctx hlong cp.a ⟨1, Γ.act_one _⟩).2
  have hfirstCard := nine_next_center_order_of_initial_four ctx.toLocalContext hfour
  have hcomm := nine_eight_contained_center_commutator ctx hlong neighbor hneighbor hcontained hnoncomm
  have hWcomm := nine_eight_contained_center_neighborhood_commutator ctx hb hcontain
    neighbor hneighbor hcontained hindex hnot hnoncomm
  have hWabelian : IsMulCommutative W := nine_eight_neighborhood_abelian ctx.toLocalContext
    (by have hge := nine_ten_length_ge_five ctx.toLocalContext hb; change 5 ≤ cp.length at hge; change 4 < cp.length; omega) cp.a
  have hZW : ZAt Γ cp.a ≤ W :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1.trans
      (nine_eight_v_le_generated_neighborhood Γ
        ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj))
  have hfirstW : Zfirst ≤ W :=
    (((nine_seven_center_join ctx cp.a ⟨1, Γ.act_one _⟩).2 cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2.trans hZW)
  have hterminalW : Zterminal ≤ W :=
    hcontain.trans (nine_eight_v_le_generated_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj))
  have hRW : R ≤ W := sup_le hfirstW hterminalW
  have hterminalC : Zterminal ≤ Subgroup.centralizer (W : Set G) :=
    hterminalW.trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr hWabelian)
  obtain ⟨alignment, halign, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpen := (nine_three_initial_extraction_inputs ctx.toLocalContext hlong).1
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a' hpen hneighbor
  have horbit : IsConjugateVertex Γ cp.a neighbor := by
    refine ⟨alignment * (actor : G), ?_⟩
    rw [Γ.act_mul, halign]
    exact hactor
  have hneighborCard := (lemma_nine_three_ambient ctx hlong neighbor horbit).2
  have hterminalCard := (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext
    hfour cp.a' ⟨alignment, hterminal⟩).1
  have hreverse : cp.a' ∈ neighborhood Γ neighbor := (mem_neighborhood_iff_adjacent Γ).mpr
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))
  have hline : Zterminal ≤ Zneighbor := ((nine_seven_center_join ctx neighbor horbit).2 cp.a' hreverse).2
  change Nat.card Zterminal = 2 at hterminalCard
  change Nat.card Zneighbor = 4 at hneighborCard
  have hlineIndex : Zterminal.relIndex Zneighbor = 2 := by
    have hmul := (Zterminal.subgroupOf Zneighbor).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hline).toEquiv,
      hterminalCard, hneighborCard] at hmul
    change (Zterminal.subgroupOf Zneighbor).index = 2
    omega
  have hRindex : Zfirst.relIndex R ≤ 2 := by
    have hnorm : Zterminal ≤ Subgroup.normalizer (Zfirst : Set G) :=
      ((hterminalW.trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr hWabelian)).trans
        (Subgroup.centralizer_le hfirstW)).trans (Subgroup.centralizer_le_normalizer _)
    have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Zfirst Zterminal hnorm
    change Nat.card Zfirst = 2 at hfirstCard
    change Nat.card Zterminal = 2 at hterminalCard
    rw [hfirstCard, hterminalCard] at hprod
    have hpositive : 0 < Nat.card (Zfirst ⊓ Zterminal : Subgroup G) := Nat.card_pos
    have hRcard : Nat.card R ≤ 4 := by change Nat.card (Zfirst ⊔ Zterminal : Subgroup G) ≤ 4; nlinarith
    have hmul := (Zfirst.subgroupOf R).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Zfirst ≤ R from le_sup_left)).toEquiv,
      hfirstCard] at hmul
    change Zfirst.relIndex R * 2 = Nat.card R at hmul
    omega
  obtain ⟨K, hKV, hKcard, hKcomm⟩ := Subgroup.exists_large_subgroup_commutator_le_of_index_two
    Vprev W Zneighbor Zterminal Zfirst R
    (nine_eight_v_le_generated_neighborhood Γ hprevious) hWabelian hRW hWcomm hline hterminalC hlineIndex
  have hneighborV : Zneighbor ≤ VAt Γ cp.a' := by
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hneighborFirst := hneighborV.trans (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hmax := nine_nine_maximal_le_intersection_of_edge ctx hb Zneighbor
    (le_inf hcontained hneighborFirst) (by rw [Subgroup.commutator_comm]; exact hcomm)
    previous hprevious hne
  have hKmax := (le_nineNineCommutatorBound_iff Vprev Zneighbor Zfirst K
    (nine_nine_previous_normalizes_first_center ctx.toLocalContext hb previous hprevious)).mpr ⟨hKV,hKcomm⟩
  exact hKcard.trans ((Nat.mul_le_mul_right _ hRindex).trans
    (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le (hKmax.trans hmax))))


public theorem nine_eight_distinct_neighbor_modules
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep) :
    VAt ctx.Γ previous ≠ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  intro heq
  have hmodel := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).1
  have hprevAdj := (mem_neighborhood_iff_adjacent Γ).mp hprevious
  have hsame (neighbor : Γ.Vertex) (hneighbor : neighbor ∈ Neighborhood Γ cp.a) :
      VAt Γ neighbor = VAt Γ previous := by
    by_cases heqPrev : neighbor = previous
    · rw [heqPrev]
    obtain ⟨mover, hmovePrev, _, hmoveFirst⟩ := nine_seven_two_arc_transport ctx.sectionSeven Γ
      hprevAdj cp.firstStep_adj hne hprevAdj
      ((mem_neighborhood_iff_adjacent Γ).mp hneighbor) (fun h => heqPrev h.symm)
      ⟨1, Γ.act_one _⟩ hmodel
    have hmap := congrArg (fun subgroup : Subgroup G =>
      subgroup.map (MulAut.conj mover⁻¹).toMonoidHom) heq
    change (v Γ previous).map _ = (v Γ cp.firstStep).map _ at hmap
    rw [← v_act, ← v_act, hmovePrev, hmoveFirst] at hmap
    exact hmap.symm
  have hneModule : VAt Γ previous ≠ ⊥ := by
    have hZa : ZAt Γ cp.a ≤ VAt Γ previous :=
      nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hprevAdj)
    intro hbot
    have hZbot := le_bot_iff.mp (hbot ▸ hZa)
    have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).2
    rw [hZbot, Subgroup.card_bot] at hfour
    omega
  apply nine_seven_module_not_normalized_by_neighbor ctx.toLocalContext hb
    (Γ.adjacent_symm hprevAdj) hneModule
  have hjoin : GeneratedNeighborhoodV Γ cp.a = VAt Γ previous := by
    apply le_antisymm
    · rw [GeneratedNeighborhoodV]
      apply sSup_le
      rintro subgroup ⟨neighbor,hneighbor,rfl⟩
      exact (hsame neighbor hneighbor).le
    · exact nine_eight_v_le_generated_neighborhood Γ hprevious
  change GAt Γ cp.a ≤ Subgroup.normalizer (VAt Γ previous : Set G)
  rw [← hjoin]
  exact nine_seven_stabilizer_normalizes_neighborhood Γ cp.a

public theorem nine_eight_contained_center_backward_index
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
    (hnoncomm : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep) :
    QuotientCardEq (VAt ctx.Γ previous)
      (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep) 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Vprev := VAt Γ previous
  let Vfirst := VAt Γ cp.firstStep
  let I := Vprev ⊓ Vfirst
  have hbound := nine_eight_contained_center_backward_bound ctx hb hcontain neighbor hneighbor
    hcontained hindex hnot hnoncomm previous hprevious hne
  change Nat.card Vprev ≤ 2 * Nat.card I at hbound
  have hlong : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hmodulesNe := nine_eight_distinct_neighbor_modules ctx hlong previous hprevious hne
  obtain ⟨mover, hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  have hcards : Nat.card Vprev = Nat.card Vfirst := by
    change Nat.card (v Γ previous) = Nat.card (v Γ cp.firstStep)
    rw [← hmove, v_act]
    exact Subgroup.card_map_of_injective (MulAut.conj (mover : G)⁻¹).injective
  have hproper : ¬ Vprev ≤ I := by
    intro hle
    apply hmodulesNe
    exact Subgroup.eq_of_le_of_card_ge (hle.trans inf_le_right) hcards.ge
  have hnotOne : I.relIndex Vprev ≠ 1 := by
    intro heq
    exact hproper (Subgroup.relIndex_eq_one.mp heq)
  have hmul := (I.subgroupOf Vprev).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show I ≤ Vprev from inf_le_left)).toEquiv]
    at hmul
  change I.relIndex Vprev * Nat.card I = Nat.card Vprev at hmul
  have hIpos : 0 < Nat.card I := Nat.card_pos
  have hVpos : 0 < Nat.card Vprev := Nat.card_pos
  have hindexTwo : I.relIndex Vprev = 2 := by
    have hupper : I.relIndex Vprev ≤ 2 := by nlinarith
    have hpositive : I.relIndex Vprev ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hmul
      omega
    omega
  change Nat.card Vprev = 2 * Nat.card I
  simpa only [hindexTwo] using hmul.symm

end Stellmacher.SectionNine
