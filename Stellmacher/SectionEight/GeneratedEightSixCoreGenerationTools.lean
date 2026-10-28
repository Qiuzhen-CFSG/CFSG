module

public import Stellmacher.SectionEight.GeneratedEightSixEquationOneCoreTools
public import Stellmacher.SectionEight.GeneratedEightSixSylowIntersection

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_generation_core_eq_inter
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex)
    (hprevious : previous ∈ neighborhood graph path.a)
    (L Q : Subgroup G)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L) : Q = L ⊓ QAt graph path.a := by
  have hclosure := eight_six_previous_closure_containments hyp graph path previous hprevious
  rw [← hL] at hclosure
  have hnormal : NormalIn L (GAt graph path.a) := by
    refine ⟨hclosure.1, Subgroup.normal_subgroupOf_of_le_normalizer ?_⟩
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  rw [hQ, eight_six_core_of_normal_eq_inter _ _ hnormal]
  rw [QAt, q, graph.twoCoreAt_def]
  rfl

public theorem eight_six_generation_neighbor_core_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (neighbor : graph.Vertex) (hadj : neighbor ∈ neighborhood graph path.a) :
    QAt graph path.a ≤ GAt graph neighbor ∧
      QAt graph neighbor ≤ GAt graph path.a := by
  have hback : path.a ∈ neighborhood graph neighbor :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hadj))
  exact ⟨((lemma_seven_three hyp graph).sylow_and_core path.a neighbor hadj
    (default : Sylow 2 (↥(GAt graph path.a ⊓ GAt graph neighbor)))).2.2,
    ((lemma_seven_three hyp graph).sylow_and_core neighbor path.a hback
    (default : Sylow 2 (↥(GAt graph neighbor ⊓ GAt graph path.a)))).2.2⟩

public theorem eight_six_generation_neighbor_module_le_closure
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length) (previous neighbor : graph.Vertex)
    (hprevious : previous ∈ neighborhood graph path.a)
    (hneighbor : neighbor ∈ neighborhood graph path.a) :
    VAt graph neighbor ≤ conjugateClosure (QAt graph previous) (GAt graph path.a) := by
  have hcore : VAt graph neighbor ≤ QAt graph neighbor :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path hlength neighbor
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one hyp graph).local_transitivity path.a hneighbor hprevious
  have hmap : QAt graph previous =
      (QAt graph neighbor).map (MulAut.conj (actor : G)⁻¹).toMonoidHom := by
    rw [← hactor]
    exact SevenSix.q_act graph actor neighbor
  intro element helement
  have hconjugate : (actor : G)⁻¹ * element * actor ∈ QAt graph previous := by
    rw [hmap]
    exact Subgroup.mem_map.mpr ⟨element, hcore helement, by simp⟩
  apply Subgroup.subset_closure
  refine ⟨actor, ⟨_, hconjugate⟩, ?_⟩
  group

public theorem eight_six_generation_neighbor_inter_le_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length) (previous neighbor : graph.Vertex)
    (hprevious : previous ∈ neighborhood graph path.a)
    (hneighbor : neighbor ∈ neighborhood graph path.a)
    (L Q : Subgroup G)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L) : VAt graph neighbor ⊓ QAt graph path.a ≤ Q := by
  rw [eight_six_generation_core_eq_inter hyp graph path previous hprevious L Q hL hQ]
  apply inf_le_inf_right
  rw [hL]
  exact eight_six_generation_neighbor_module_le_closure
    hyp graph path hlength previous neighbor hprevious hneighbor

public theorem eight_six_generation_lower_bound
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length) (previous : graph.Vertex)
    (hprevious : previous ∈ neighborhood graph path.a)
    (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData graph path D L Q) :
    (VAt graph previous ⊓ QAt graph path.a) ⊔
      (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D ≤ Q := by
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  exact sup_le (sup_le
    (eight_six_generation_neighbor_inter_le_core hyp graph path hlength
      previous previous hprevious hprevious L Q hL hQ)
    (eight_six_generation_neighbor_inter_le_core hyp graph path hlength
      previous path.firstStep hprevious hfirst L Q hL hQ))
    (eight_six_action_core_containments hyp graph path previous hprevious
      D L Q hD hL hQ action).1

public theorem eight_six_generation_neighbor_action
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length) (neighbor : graph.Vertex)
    (hadj : neighbor ∈ neighborhood graph path.a) :
    QAt graph path.a ≤
        Subgroup.normalizer ((VAt graph neighbor ⊓ QAt graph path.a : Subgroup G) : Set G) ∧
      ⁅QAt graph path.a, VAt graph neighbor⁆ ≤
        VAt graph neighbor ⊓ QAt graph path.a := by
  have hcores := eight_six_generation_neighbor_core_le hyp graph path neighbor hadj
  have hcore : VAt graph neighbor ≤ QAt graph neighbor :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path hlength neighbor
  have hnormalV : QAt graph path.a ≤ Subgroup.normalizer (VAt graph neighbor : Set G) :=
    hcores.1.trans (stabilizer_le_normalizer_v graph neighbor)
  have hnormalQ : VAt graph neighbor ≤ Subgroup.normalizer (QAt graph path.a : Set G) :=
    (hcore.trans hcores.2).trans (SevenSix.stabilizer_le_normalizer_q graph path.a)
  exact ⟨(le_inf hnormalV (QAt graph path.a).le_normalizer).trans
    Subgroup.inf_normalizer_le_normalizer_inf,
    le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp hnormalV)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalQ)⟩

public theorem eight_six_generation_neighbor_inter_le_orbit
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (neighbor : graph.Vertex) (hadj : neighbor ∈ neighborhood graph path.a) :
    VAt graph neighbor ⊓ QAt graph path.a ≤
      conjugateClosure (VAt graph path.firstStep ⊓ QAt graph path.a)
        (GAt graph path.a) := by
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one hyp graph).local_transitivity path.a hfirst hadj
  have hcoremap : (QAt graph path.a).map (MulAut.conj (actor : G)⁻¹).toMonoidHom =
      QAt graph path.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (SevenSix.stabilizer_le_normalizer_q graph path.a
        ((GAt graph path.a).inv_mem actor.property))
  have hvmap : VAt graph neighbor =
      (VAt graph path.firstStep).map (MulAut.conj (actor : G)⁻¹).toMonoidHom := by
    rw [← hactor]
    exact v_act graph actor path.firstStep
  have hintermap : VAt graph neighbor ⊓ QAt graph path.a =
      (VAt graph path.firstStep ⊓ QAt graph path.a).map
        (MulAut.conj (actor : G)⁻¹).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (actor : G)⁻¹).injective,
      ← hvmap, hcoremap]
  rw [hintermap]
  rintro element ⟨representative, hrepresentative, rfl⟩
  apply Subgroup.subset_closure
  exact ⟨actor⁻¹, ⟨representative, hrepresentative⟩, by simp⟩

public theorem eight_six_generation_orbit_le_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length) (previous : graph.Vertex)
    (hprevious : previous ∈ neighborhood graph path.a)
    (L Q : Subgroup G)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L) :
    conjugateClosure (VAt graph path.firstStep ⊓ QAt graph path.a)
      (GAt graph path.a) ≤ Q := by
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  apply eight_six_conjugate_closure_le _ _ _
    (eight_six_generation_neighbor_inter_le_core hyp graph path hlength
      previous path.firstStep hprevious hfirst L Q hL hQ)
  rw [eight_six_generation_core_eq_inter hyp graph path previous hprevious L Q hL hQ]
  apply le_trans (le_inf ?_ (SevenSix.stabilizer_le_normalizer_q graph path.a))
    Subgroup.inf_normalizer_le_normalizer_inf
  rw [hL]
  exact eight_six_conjugate_closure_normalizer _ _

public theorem eight_six_generation_of_orbit_bounds
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length) (previous : graph.Vertex)
    (hprevious : previous ∈ neighborhood graph path.a)
    (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData graph path D L Q)
    (hcover : Q ≤ conjugateClosure
      (VAt graph path.firstStep ⊓ QAt graph path.a) (GAt graph path.a) ⊔ D)
    (hspan : conjugateClosure
      (VAt graph path.firstStep ⊓ QAt graph path.a) (GAt graph path.a) ≤
      (VAt graph previous ⊓ QAt graph path.a) ⊔
        (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D) :
    Q = (VAt graph previous ⊓ QAt graph path.a) ⊔
      (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D := by
  exact le_antisymm (hcover.trans (sup_le hspan le_sup_right))
    (eight_six_generation_lower_bound hyp graph path hlength previous hprevious
      D L Q hD hL hQ action)

end Stellmacher.SectionEight
