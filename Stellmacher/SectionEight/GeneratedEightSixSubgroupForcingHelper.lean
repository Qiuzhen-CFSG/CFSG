module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup
public import Stellmacher.SectionNine.CubicLocalAction

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement

universe u

public theorem eight_six_commutator_le_conjugate_core
    {G : Type u} [Group G] (B D U actors : Subgroup G)
    (hUB : U ≤ B) (hDB : D ≤ B) (hcomm : ⁅U, actors⁆ ≤ D)
    (actor : G) (hactor : actor ∈ actors) :
    U ≤ B ⊓ B.map (MulAut.conj actor⁻¹).toMonoidHom := by
  refine le_inf hUB ?_
  intro element helement
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]
  have hbracket : ⁅actor, element⁆ ∈ D := by
    rw [← commutatorElement_inv]
    exact D.inv_mem (hcomm (Subgroup.commutator_mem_commutator helement hactor))
  simpa [commutatorElement_def, mul_assoc] using
    B.mul_mem (hDB hbracket) (hUB helement)

public theorem eight_six_neighbor_core_le_closure
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (initial previous neighbor : graph.Vertex)
    (hprevious : previous ∈ Neighborhood graph initial)
    (hneighbor : neighbor ∈ Neighborhood graph initial) :
    QAt graph neighbor ≤ conjugateClosure (QAt graph previous) (GAt graph initial) := by
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one hyp graph).local_transitivity initial hprevious hneighbor
  rw [← hactor]
  change q graph (graph.act actor previous) ≤ _
  rw [SevenSix.q_act]
  rintro element ⟨generator, hgenerator, rfl⟩
  apply Subgroup.subset_closure
  exact ⟨⟨(actor : G)⁻¹, (GAt graph initial).inv_mem actor.property⟩,
    ⟨generator, hgenerator⟩, by simp⟩

public theorem eight_six_intersection_initial_core_le_closure_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (initial : graph.Vertex)
    (L : Subgroup G) (hL : L ≤ GAt graph initial) :
    L ⊓ QAt graph initial ≤ twoCoreIn L := by
  have hnormal : ((L ⊓ QAt graph initial).subgroupOf L).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact (le_inf L.le_normalizer
      (hL.trans (SevenSix.stabilizer_le_normalizer_q graph initial))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have htwo : IsPGroup 2 (L ⊓ QAt graph initial : Subgroup G) := by
    have hcore : IsPGroup 2 (QAt graph initial) := by
      change IsPGroup 2 (graph.twoCoreAt initial)
      rw [graph.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact hcore.to_le inf_le_right
  have hnative : IsPGroup 2 ((L ⊓ QAt graph initial).subgroupOf L) :=
    htwo.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hle : (L ⊓ QAt graph initial).subgroupOf L ≤ pCore 2 L :=
    le_sSup ⟨hnormal, hnative⟩
  calc
    L ⊓ QAt graph initial = ((L ⊓ QAt graph initial).subgroupOf L).map L.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm
    _ ≤ _ := Subgroup.map_mono hle

public theorem eight_six_cubic_opposite_core_intersection
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (initial first previous third : graph.Vertex)
    (hquot : QuotientIsModel (GAt graph initial) (QAt graph initial) SL2Two)
    (hfirst : first ∈ Neighborhood graph initial)
    (hprevious : previous ∈ Neighborhood graph initial)
    (hthird : third ∈ Neighborhood graph initial)
    (hprevne : previous ≠ first) (hthirdne : third ≠ previous)
    (D : Subgroup G) (hD : D = QAt graph previous ⊓ QAt graph first)
    (hnormal : NormalIn D (GAt graph initial)) :
    QAt graph previous ⊓ QAt graph third = D := by
  have cubic := SectionNine.cubic_local_action_of_sl2Two_quotient graph hyp initial hquot
  let edge := GAt graph initial ⊓ GAt graph previous
  have hnot : ¬ edge ≤ QAt graph initial := by
    intro hle
    have hcard := cubic.edge_card previous
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hprevious)
    have hbound := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    have hpositive : 0 < Nat.card (QAt graph initial) := Nat.card_pos
    change Nat.card edge = 2 * Nat.card (QAt graph initial) at hcard
    omega
  have htrans := cubic.punctured_transitivity previous
    ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hprevious) edge le_rfl hnot
  obtain ⟨actor, hactor⟩ := htrans
    (d := first) (l := third) ⟨hfirst, hprevne.symm⟩ ⟨hthird, hthirdne⟩
  have hfix : graph.act (actor : G) previous = previous :=
    (Set.ext_iff.mp (graph.stabilizer_def previous) actor).mp actor.property.2
  have hDmap : D.map (MulAut.conj (actor : G)⁻¹).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (D : Set G)).inv_mem
        (((Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2)
          actor.property.1))
  rw [← hDmap, hD, Subgroup.map_inf _ _ _ (MulAut.conj (actor : G)⁻¹).injective]
  change q graph previous ⊓ q graph third = _
  rw [← SevenSix.q_act, ← SevenSix.q_act, hfix, hactor]

public theorem eight_six_cubic_subgroup_forcing
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (initial first previous : graph.Vertex)
    (hquot : QuotientIsModel (GAt graph initial) (QAt graph initial) SL2Two)
    (hfirst : first ∈ Neighborhood graph initial)
    (hprevious : previous ∈ Neighborhood graph initial)
    (hprevne : previous ≠ first)
    (D : Subgroup G) (hD : D = QAt graph previous ⊓ QAt graph first)
    (hnormal : NormalIn D (GAt graph initial))
    (actor : G) (hactor : actor ∈ QAt graph first)
    (houtside : actor ∉ QAt graph initial)
    (U : Subgroup G) (hU : U ≤ QAt graph previous)
    (hcomm : ⁅U, Subgroup.zpowers actor⁆ ≤ D) : U ≤ D := by
  classical
  let neighbors := {neighbor // graph.adjacent initial neighbor}
  let _ : Finite graph.Vertex := graph.finiteVertex
  let _ := Fintype.ofFinite neighbors
  have cubic := SectionNine.cubic_local_action_of_sl2Two_quotient graph hyp initial hquot
  let firstNeighbor : neighbors :=
    ⟨first, (SevenSix.mem_neighborhood_iff_adjacent graph).mp hfirst⟩
  let previousNeighbor : neighbors :=
    ⟨previous, (SevenSix.mem_neighborhood_iff_adjacent graph).mp hprevious⟩
  have hexists : ∃ third : neighbors, third ≠ firstNeighbor ∧ third ≠ previousNeighbor := by
    by_contra! hnone
    have hcover : (Finset.univ : Finset neighbors) ⊆ {firstNeighbor, previousNeighbor} := by
      intro member _
      by_cases hfirst : member = firstNeighbor
      · simp [hfirst]
      · simp [hnone member hfirst]
    have hbound := Finset.card_le_card hcover
    have hcard : Fintype.card neighbors = 3 := by
      rw [← Nat.card_eq_fintype_card]
      exact cubic.degree
    have hpair : ({firstNeighbor, previousNeighbor} : Finset neighbors).card ≤ 2 :=
      Finset.card_insert_le _ _ |>.trans (by simp)
    simp only [Finset.card_univ, hcard] at hbound
    omega
  obtain ⟨third, hthirdFirst, hthirdPrevious⟩ := hexists
  have hthird : (third : graph.Vertex) ∈ Neighborhood graph initial :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr third.property
  have hthirdne : (third : graph.Vertex) ≠ previous :=
    fun heq => hthirdPrevious (Subtype.ext heq)
  have hfirstCore : QAt graph first ≤ GAt graph initial ⊓ GAt graph first := by
    apply le_inf
    · exact ((lemma_seven_three hyp graph).sylow_and_core first initial
        ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr
          (graph.adjacent_symm firstNeighbor.property)) default).2.2
    · change graph.twoCoreAt first ≤ graph.vertexStabilizer first
      rw [graph.twoCoreAt_def]
      exact SevenSix.twoCoreIn_le _
  have hcyclic : Subgroup.zpowers actor ≤ GAt graph initial ⊓ GAt graph first :=
    Subgroup.zpowers_le.mpr (hfirstCore hactor)
  have hnot : ¬ Subgroup.zpowers actor ≤ QAt graph initial :=
    fun hle => houtside (hle (Subgroup.mem_zpowers actor))
  have htrans := cubic.punctured_transitivity first firstNeighbor.property
    (Subgroup.zpowers actor) hcyclic hnot
  obtain ⟨mover, hmover⟩ := htrans (d := previous) (l := third)
    ⟨hprevious, hprevne⟩ ⟨hthird, fun heq => hthirdFirst (Subtype.ext heq)⟩
  have hbound := eight_six_commutator_le_conjugate_core
    (QAt graph previous) D U (Subgroup.zpowers actor) hU (hD ▸ inf_le_left)
      hcomm mover mover.property
  have hmap : (QAt graph previous).map (MulAut.conj (mover : G)⁻¹).toMonoidHom =
      QAt graph third := by
    change (q graph previous).map _ = q graph third
    rw [← SevenSix.q_act, hmover]
  rw [hmap, eight_six_cubic_opposite_core_intersection hyp graph initial first previous
    third hquot hfirst hprevious hthird hprevne hthirdne D hD hnormal] at hbound
  exact hbound

public theorem generated_eight_six_quotient_action_forcing
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (_hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (_hlength : ctx.criticalPath.length = 2)
    (_hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (_hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (equation : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (actor : (P1 ⊔ P2 : Subgroup H))
    (hactor : actor ∈ QAt ctx.Γ ctx.criticalPath.firstStep) (houtside : actor ∉ Q)
    (U : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hU : U ≤ QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅U, Subgroup.zpowers actor⁆ ≤ D) : U ≤ D := by
  have hfirst : ctx.criticalPath.firstStep ∈ Neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  have hnextL : QAt ctx.Γ ctx.criticalPath.firstStep ≤ L := by
    rw [hdefs.2.1]
    exact eight_six_neighbor_core_le_closure ctx.sectionSeven ctx.Γ
      ctx.criticalPath.a previous ctx.criticalPath.firstStep hprev.1 hfirst
  have hnot : actor ∉ QAt ctx.Γ ctx.criticalPath.a := by
    intro hcore
    apply houtside
    rw [hdefs.2.2.1]
    exact eight_six_intersection_initial_core_le_closure_core ctx.Γ
      ctx.criticalPath.a L equation.closure_le ⟨hnextL hactor, hcore⟩
  exact eight_six_cubic_subgroup_forcing ctx.sectionSeven ctx.Γ ctx.criticalPath.a
    ctx.criticalPath.firstStep previous hquot hfirst hprev.1 hprev.2 D hdefs.1
    equation.intersection_normal actor hactor hnot U (hU.trans inf_le_left) hcomm


end Stellmacher.SectionEight
