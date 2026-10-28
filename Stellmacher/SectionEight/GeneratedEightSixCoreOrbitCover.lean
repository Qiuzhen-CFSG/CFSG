module
public import Stellmacher.SectionEight.GeneratedEightSixCoreGenerationTools
public import Stellmacher.SectionEight.GeneratedEightSixNeighborCorePart
public import Stellmacher.SectionEight.SL2CentralizingSeedCore

/-!
# Core orbit coverage in Stellmacher (8.6)(1)

The two-core Q of the actual previous-core closure lies in the join of D
with the initial-stabilizer conjugate closure of the first neighbor-module
core part. The exact local graph, length-two hypothesis, initial SL₂(2)
quotient, subgroup definitions and already proved action data are retained.

The neighbor-core identity first puts the first-step core inside its neighbor
module joined with D. Transport and normality of D then put L in the module's
conjugate closure joined with D. The abstract centralizing-seed theorem for
an SL₂(2) quotient bounds that module closure's intersection with the initial
core. Factoring an element of Q and using D's core containment gives the
required coverage. No three-factor generation, Frattini conclusion, or later
case classification is assumed.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.41, equation (1)
in the proof of (8.6); `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped Pointwise
universe u
private theorem eight_six_cover_first_seed_le_of_core_part
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
    (hpart : QAt graph path.firstStep ⊓ QAt graph path.a ≤
      (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D) :
    QAt graph path.firstStep ≤ VAt graph path.firstStep ⊔ D := by
  have hcores := eight_six_action_core_containments hyp graph path previous
    hprevious D L Q hD hL hQ action
  have hQnormal : GAt graph path.a ≤ Subgroup.normalizer (Q : Set G) := by
    rw [eight_six_generation_core_eq_inter hyp graph path previous hprevious L Q hL hQ]
    apply (le_inf ?_ (SevenSix.stabilizer_le_normalizer_q graph path.a)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hVcore : VAt graph path.firstStep ≤ QAt graph path.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path hlength _
  have hVnormal : VAt graph path.firstStep ≤ Subgroup.normalizer (Q : Set G) :=
    (hVcore.trans (eight_six_generation_neighbor_core_le hyp graph path
      path.firstStep hfirst).2).trans hQnormal
  have hfirstL : QAt graph path.firstStep ≤ L := by
    rw [hL]
    exact eight_six_first_core_le_previous_closure hyp graph path previous hprevious
  have hfirstS : QAt graph path.firstStep ≤ S :=
    (SevenSix.local_cores_le_edge_sylow hyp graph path).2
  intro element helement
  have hsupp : element ∈ VAt graph path.firstStep ⊔ Q :=
    action.sylow_intersection ▸ ⟨hfirstL helement, hfirstS helement⟩
  have hproduct : element ∈ (VAt graph path.firstStep : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVnormal]
    exact hsupp
  obtain ⟨first, hfirstV, core, hcoreQ, rfl⟩ := hproduct
  have hcoreFirst : core ∈ QAt graph path.firstStep := by
    simpa only [inv_mul_cancel_left] using (QAt graph path.firstStep).mul_mem
      ((QAt graph path.firstStep).inv_mem (hVcore hfirstV)) helement
  have hpartTarget : (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D ≤
      VAt graph path.firstStep ⊔ D := sup_le_sup inf_le_left le_rfl
  have hcoreTarget : core ∈ VAt graph path.firstStep ⊔ D :=
    hpartTarget (hpart ⟨hcoreFirst, hcores.2.1 hcoreQ⟩)
  exact (VAt graph path.firstStep ⊔ D).mul_mem
    ((le_sup_left : VAt graph path.firstStep ≤ VAt graph path.firstStep ⊔ D) hfirstV)
    hcoreTarget

private theorem eight_six_cover_closure_le_module_closure_sup
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (hprevious : previous ∈ neighborhood graph path.a)
    (D L : Subgroup G)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hnormal : NormalIn D (GAt graph path.a))
    (hseed : QAt graph path.firstStep ≤ VAt graph path.firstStep ⊔ D) :
    L ≤ conjugateClosure (VAt graph path.firstStep) (GAt graph path.a) ⊔ D := by
  let container := conjugateClosure (VAt graph path.firstStep) (GAt graph path.a) ⊔ D
  have hnormalContainer : GAt graph path.a ≤ Subgroup.normalizer (container : Set G) :=
    (le_inf (eight_six_conjugate_closure_normalizer _ _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hfirstContainer : QAt graph path.firstStep ≤ container := by
    apply hseed.trans
    apply sup_le_sup _ le_rfl
    intro element helement
    exact Subgroup.subset_closure ⟨1, ⟨element, helement⟩, by simp⟩
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  obtain ⟨actor, hactor⟩ := (lemma_seven_one hyp graph).local_transitivity
    path.a hfirst hprevious
  have hpreviousContainer : QAt graph previous ≤ container := by
    rw [← hactor]
    change (q graph (graph.act actor path.firstStep)) ≤ container
    rw [SevenSix.q_act]
    rintro element ⟨representative, hrepresentative, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (hnormalContainer ((GAt graph path.a).inv_mem actor.property)) _).mp
        (hfirstContainer hrepresentative)
  rw [hL]
  exact eight_six_conjugate_closure_le _ _ _ hpreviousContainer hnormalContainer

private theorem eight_six_cover_of_core_part_and_module_closure
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
    (hpart : QAt graph path.firstStep ⊓ QAt graph path.a ≤
      (VAt graph path.firstStep ⊓ QAt graph path.a) ⊔ D)
    (hclosure : conjugateClosure (VAt graph path.firstStep) (GAt graph path.a) ⊓
      QAt graph path.a ≤ conjugateClosure
        (VAt graph path.firstStep ⊓ QAt graph path.a) (GAt graph path.a)) :
    Q ≤ conjugateClosure (VAt graph path.firstStep ⊓ QAt graph path.a)
      (GAt graph path.a) ⊔ D := by
  let moduleClosure := conjugateClosure (VAt graph path.firstStep) (GAt graph path.a)
  let orbit := conjugateClosure (VAt graph path.firstStep ⊓ QAt graph path.a)
    (GAt graph path.a)
  have hcores := eight_six_action_core_containments hyp graph path previous hprevious
    D L Q hD hL hQ action
  have hseed := eight_six_cover_first_seed_le_of_core_part hyp graph path hlength
    previous hprevious D L Q hD hL hQ action hpart
  have hLbound := eight_six_cover_closure_le_module_closure_sup hyp graph path
    previous hprevious D L hL action.intersection_normal hseed
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hVinitial := (SevenSix.neighbor_join_le_core_of_length_gt_one
    graph path hlength path.firstStep).trans
      (eight_six_generation_neighbor_core_le hyp graph path path.firstStep hfirst).2
  have hmoduleInitial : moduleClosure ≤ GAt graph path.a :=
    eight_six_conjugate_closure_le _ _ _ hVinitial (GAt graph path.a).le_normalizer
  have hnormalD : moduleClosure ≤ Subgroup.normalizer (D : Set G) :=
    hmoduleInitial.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      action.intersection_normal.1).mp action.intersection_normal.2)
  intro element helement
  have hproduct : element ∈ (moduleClosure : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnormalD]
    exact hLbound ((hQ ▸ SevenSix.twoCoreIn_le L) helement)
  obtain ⟨member, hmember, part, hpartD, rfl⟩ := hproduct
  have hmemberCore : member ∈ QAt graph path.a := by
    simpa only [mul_inv_cancel_right] using (QAt graph path.a).mul_mem
      (hcores.2.1 helement) ((QAt graph path.a).inv_mem
        (hcores.2.1 (hcores.1 hpartD)))
  exact (orbit ⊔ D).mul_mem
    ((le_sup_left : orbit ≤ orbit ⊔ D) (hclosure ⟨hmember, hmemberCore⟩))
    ((le_sup_right : D ≤ orbit ⊔ D) hpartD)

private theorem eight_six_cover_module_closure_of_sl2_seed_theorem
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length) (previous : graph.Vertex)
    (hprevious : previous ∈ neighborhood graph path.a)
    (L Q : Subgroup G)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L)
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    :
    conjugateClosure (VAt graph path.firstStep) (GAt graph path.a) ⊓
      QAt graph path.a ≤ conjugateClosure
        (VAt graph path.firstStep ⊓ QAt graph path.a) (GAt graph path.a) := by
  let orbit := conjugateClosure (VAt graph path.firstStep ⊓ QAt graph path.a)
    (GAt graph path.a)
  have hcore : QAt graph path.a = twoCoreIn (GAt graph path.a) :=
    graph.twoCoreAt_def _
  have hcoreLe : QAt graph path.a ≤ GAt graph path.a :=
    hcore.le.trans (SevenSix.twoCoreIn_le _)
  have hcoreNormal : NormalIn (QAt graph path.a) (GAt graph path.a) :=
    ⟨hcoreLe, Subgroup.normal_subgroupOf_of_le_normalizer
      (SevenSix.stabilizer_le_normalizer_q graph path.a)⟩
  have hcoreTwo : IsPGroup 2 (QAt graph path.a) :=
    hcore ▸ eight_six_two_core_is_two_group _
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hVcore : VAt graph path.firstStep ≤ QAt graph path.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path hlength _
  have hVinitial := hVcore.trans
    (eight_six_generation_neighbor_core_le hyp graph path path.firstStep hfirst).2
  have hVtwo : IsPGroup 2 (VAt graph path.firstStep) := by
    apply IsPGroup.to_le (K := QAt graph path.firstStep) _ hVcore
    change IsPGroup 2 (graph.twoCoreAt path.firstStep)
    rw [graph.twoCoreAt_def]
    exact eight_six_two_core_is_two_group _
  have horbitCore : orbit ≤ QAt graph path.a :=
    (eight_six_generation_orbit_le_core hyp graph path hlength previous hprevious
      L Q hL hQ).trans
      ((eight_six_generation_core_eq_inter hyp graph path previous hprevious
        L Q hL hQ).le.trans inf_le_right)
  have horbitNormal : NormalIn orbit (GAt graph path.a) :=
    ⟨horbitCore.trans hcoreLe, Subgroup.normal_subgroupOf_of_le_normalizer
      (eight_six_conjugate_closure_normalizer _ _)⟩
  have hinter : VAt graph path.firstStep ⊓ QAt graph path.a ≤ orbit := by
    intro element helement
    exact Subgroup.subset_closure ⟨1, ⟨element, helement⟩, by simp⟩
  exact sl2_centralizing_seed_closure_core_le _ _ _ _ hcoreNormal hcoreTwo hquot hVinitial hVtwo
    horbitNormal horbitCore ((eight_six_generation_neighbor_action hyp graph path
      hlength path.firstStep hfirst).2.trans hinter) hinter

public theorem eight_six_core_orbit_cover_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q) :
    Q ≤ conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a) ⊔ D := by
  have hcores := eight_six_action_core_containments ctx.sectionSeven ctx.Γ
    ctx.criticalPath previous hprev.1 D L Q hD hL hQ action
  have hpart := eight_six_neighbor_core_part_local ctx hquot hlength previous hprev D
    hD action.intersection_normal (hcores.1.trans hcores.2.1)
  apply eight_six_cover_of_core_part_and_module_closure ctx.sectionSeven ctx.Γ
    ctx.criticalPath (by omega) previous hprev.1 D L Q hD hL hQ action hpart.le
  exact eight_six_cover_module_closure_of_sl2_seed_theorem ctx.sectionSeven ctx.Γ
    ctx.criticalPath (by omega) previous hprev.1 L Q hL hQ hquot

end Stellmacher.SectionEight
