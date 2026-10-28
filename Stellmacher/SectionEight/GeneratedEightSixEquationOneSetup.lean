module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup
public import Stellmacher.SectionFiveToSeven.Result7_6

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public structure EightSixEquationOneActionData
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (D L Q : Subgroup G) : Prop where
  intersection_normal : NormalIn D (GAt graph path.a)
  sylow_intersection : L ⊓ S = VAt graph path.firstStep ⊔ Q
  first_commutator : ⁅VAt graph path.firstStep, QAt graph path.firstStep⁆ =
    ZAt graph path.firstStep
  residual_commutator : ⁅D, twoResidualIn L⁆ = ZAt graph path.a

public theorem eight_six_initial_center_trivial_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    CenterAmbient (GAt ctx.Γ ctx.criticalPath.a) = ⊥ := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let initial := GAt graph path.a
  let first := GAt graph path.firstStep
  have hadj : path.a ∈ neighborhood graph path.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm path.firstStep_adj)
  let sylow : Sylow 2 (↥(first ⊓ initial)) := default
  have hdata := edge_sectionThree_data ctx.sectionSeven graph hadj sylow
  have hthree := lemma_seven_three ctx.sectionSeven graph
  have hcentral : z graph path.firstStep = omegaOneCenter first := by
    rcases hthree.centralizer_alternative path.firstStep path.a hadj sylow with
      hcore | hcentral
    · have hsylow : sylowTwoAmbient (first ⊓ initial) sylow ≤ first :=
        (Subgroup.map_subtype_le _).trans inf_le_left
      have hcomm : sylowTwoAmbient (first ⊓ initial) sylow ≤
          Subgroup.centralizer (z graph path.firstStep : Set G) :=
        hsylow.trans (Subgroup.le_centralizer_iff.mp
          (hcenter.trans (SevenSix.centerAmbient_le_centralizer first)))
      rw [inf_eq_left.mpr hcomm] at hcore
      exact (hdata.2.1.1.2.2.2
        (hcore.trans (graph.twoCoreAt_def path.firstStep))).elim
    · exact hcentral.1
  have hzero : Subgroup.center initial = ⊥ :=
    hthree.center_neighbor_trivial path.firstStep path.a hadj hcentral
  change (Subgroup.center initial).map initial.subtype = ⊥
  rw [hzero, Subgroup.map_bot]

public theorem eight_six_conjugate_closure_le
    {G : Type u} [Group G] (seed actors container : Subgroup G)
    (hseed : seed ≤ container)
    (hactors : actors ≤ Subgroup.normalizer (container : Set G)) :
    conjugateClosure seed actors ≤ container := by
  rw [conjugateClosure, Subgroup.closure_le]
  rintro element ⟨actor, generator, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hactors actor.property) generator).mp
    (hseed generator.property)

public theorem eight_six_conjugate_closure_normalizer
    {G : Type u} [Group G] (seed actors : Subgroup G) :
    actors ≤ Subgroup.normalizer (conjugateClosure seed actors : Set G) := by
  rw [conjugateClosure, Subgroup.le_normalizer_closure_iff]
  rintro actor hactor element ⟨other, generator, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨⟨actor * other, actors.mul_mem hactor other.property⟩, generator, ?_⟩
  simp only [mul_inv_rev]
  group

public theorem eight_six_previous_closure_containments
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex)
    (hprevious : previous ∈ Later.Neighborhood graph path.a) :
    conjugateClosure (QAt graph previous) (GAt graph path.a) ≤ GAt graph path.a ∧
      EAt graph path.a ≤
        conjugateClosure (QAt graph previous) (GAt graph path.a) := by
  let initial := GAt graph path.a
  let closure := conjugateClosure (QAt graph previous) initial
  have hback : path.a ∈ neighborhood graph previous :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm
        ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hprevious))
  let sylow : Sylow 2 (↥(GAt graph previous ⊓ initial)) := default
  have hcore : QAt graph previous ≤ initial :=
    ((lemma_seven_three hyp graph).sylow_and_core previous path.a hback sylow).2.2
  have hclosure : closure ≤ initial :=
    eight_six_conjugate_closure_le _ _ _ hcore initial.le_normalizer
  refine ⟨hclosure, ?_⟩
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one hyp graph).local_transitivity path.a hfirst hprevious
  have hmap : QAt graph previous =
      (QAt graph path.firstStep).map (MulAut.conj (actor : G)⁻¹).toMonoidHom := by
    rw [← hactor]
    exact SevenSix.q_act graph actor path.firstStep
  have hfirstClosure : QAt graph path.firstStep ≤ closure := by
    intro element helement
    have hconjugate : (actor : G)⁻¹ * element * (actor : G) ∈ QAt graph previous := by
      rw [hmap]
      exact Subgroup.mem_map.mpr ⟨element, helement, by simp⟩
    apply Subgroup.subset_closure
    refine ⟨actor, ⟨_, hconjugate⟩, ?_⟩
    group
  have hresidualCore : twoCoreIn (EAt graph path.firstStep) ≤
      QAt graph path.firstStep := by
    change twoCoreIn (graph.twoResidualAt path.firstStep) ≤ graph.twoCoreAt path.firstStep
    rw [graph.twoResidualAt_def, graph.twoCoreAt_def,
      SevenSix.residual_core_eq_inter_core]
    exact inf_le_right
  exact (lemma_seven_six hyp graph path).next_residual_core.2.trans
    (eight_six_conjugate_closure_le _ _ _ (hresidualCore.trans hfirstClosure)
      (eight_six_conjugate_closure_normalizer _ _))

public theorem eight_six_equation_one_of_action_and_core_algebra
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a)
    (D L Q : Subgroup G)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (action : EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q)
    (hgen : Q = (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D)
    (hcomm : ⁅Q, QAt ctx.Γ ctx.criticalPath.firstStep⁆ ⊔ D =
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D)
    (hfrattini : FrattiniAmbient Q ≤ D) :
    EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q := by
  have hclosure := eight_six_previous_closure_containments
    ctx.sectionSeven ctx.Γ ctx.criticalPath previous hprevious
  rw [← hL] at hclosure
  exact {
    initial_center_trivial := eight_six_initial_center_trivial_local ctx hcenter
    intersection_normal := action.intersection_normal
    closure_le := hclosure.1
    residual_le := hclosure.2
    sylow_intersection := action.sylow_intersection
    first_commutator := action.first_commutator
    residual_commutator := action.residual_commutator
    core_generation := hgen
    core_commutator := hcomm
    core_frattini_le := hfrattini }

end Stellmacher.SectionEight
