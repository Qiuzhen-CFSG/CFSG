module

public import Stellmacher.SectionEight.GeneratedEightSixFirstCommutator
public import Stellmacher.SectionEight.GeneratedEightSixEquationOneCoreTools
public import Stellmacher.SectionEight.EightTwoEdgeQuadraticAction
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore

/-!
# The Sylow intersection in generated Stellmacher (8.6)

The normality of the prescribed conjugate closure identifies its two-core
with its intersection with the initial two-core. Local transitivity puts
the first-step core, and hence its neighbor-center join, in that closure.
The order-four center action gives index two for the initial core in the
edge Sylow. At distance two, the neighbor-center join contains the critical
terminal center, so it crosses this index-two core and gives the required
Sylow supplement. Neither intersection normality nor the residual
commutator is assumed.

Source: Stellmacher, printed p.41, paragraph before (8.6)(1),
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_core_of_normal_eq_inter
    {G : Type u} [Group G] (localGroup ambientGroup : Subgroup G)
    (hnormal : NormalIn localGroup ambientGroup) :
    twoCoreIn localGroup = localGroup ⊓ twoCoreIn ambientGroup := by
  have hcoreLocal := SevenSix.twoCoreIn_le localGroup
  have hcoreAmbient := SevenSix.twoCoreIn_le ambientGroup
  have hnormalCore : NormalIn (twoCoreIn localGroup) ambientGroup :=
    ⟨hcoreLocal.trans hnormal.1,
      SevenSix.twoCoreIn_normal_of_normal _ _ hnormal.1 hnormal.2⟩
  have hle := eight_six_normal_two_subgroup_le_core _ _ hnormalCore
    (eight_six_two_core_is_two_group localGroup)
  refine le_antisymm (le_inf hcoreLocal hle) ?_
  apply eight_six_normal_two_subgroup_le_core
  · refine ⟨inf_le_left, Subgroup.normal_subgroupOf_of_le_normalizer ?_⟩
    apply le_trans (le_inf localGroup.le_normalizer
      (hnormal.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hcoreAmbient).mp
        (SevenSix.twoCoreIn_normal ambientGroup))))
    exact Subgroup.inf_normalizer_le_normalizer_inf
  · exact IsPGroup.to_le (eight_six_two_core_is_two_group ambientGroup) inf_le_right

public theorem eight_six_first_core_le_previous_closure
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (hprevious : previous ∈ neighborhood graph path.a) :
    q graph path.firstStep ≤ conjugateClosure (q graph previous) (stabilizer graph path.a) := by
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  obtain ⟨actor, hactor⟩ := (lemma_seven_one hyp graph).local_transitivity
    path.a hfirst hprevious
  have hmap : q graph previous =
      (q graph path.firstStep).map (MulAut.conj (actor : G)⁻¹).toMonoidHom := by
    rw [← hactor]
    exact SevenSix.q_act graph actor path.firstStep
  intro element helement
  have hconjugate : (actor : G)⁻¹ * element * actor ∈ q graph previous := by
    rw [hmap]
    exact Subgroup.mem_map.mpr ⟨element, helement, by simp⟩
  apply Subgroup.subset_closure
  refine ⟨actor, ⟨_, hconjugate⟩, ?_⟩
  group

public theorem eight_six_sylow_intersection_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (L Q : Subgroup G)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L) :
    L ⊓ S = VAt ctx.Γ ctx.criticalPath.firstStep ⊔ Q := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  have hlength' : path.length = 2 := hlength
  have hclosure := eight_six_previous_closure_containments
    ctx.sectionSeven graph path previous hprevious
  rw [← hL] at hclosure
  have hnormal : NormalIn L (stabilizer graph path.a) := by
    refine ⟨hclosure.1, Subgroup.normal_subgroupOf_of_le_normalizer ?_⟩
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hcore : Q = L ⊓ q graph path.a := by
    rw [hQ, eight_six_core_of_normal_eq_inter _ _ hnormal]
    rw [q, graph.twoCoreAt_def]
    rfl
  have hcores := SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path
  have hVcore : v graph path.firstStep ≤ q graph path.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) _
  have hVL : v graph path.firstStep ≤ L := by
    rw [hL]
    exact hVcore.trans (eight_six_first_core_le_previous_closure
      ctx.sectionSeven graph path previous hprevious)
  have hVS : v graph path.firstStep ≤ S := hVcore.trans hcores.2
  have hQS : Q ≤ S := (hcore.le.trans inf_le_right).trans hcores.1
  have hindex : (q graph path.a).relIndex S = 2 := by
    rw [q, graph.twoCoreAt_def]
    exact eight_two_core_relIndex_two _ _
      (SevenSix.edge_local_data ctx.sectionSeven graph path).1.1.1.2.1
      (eight_five_dihedral_action_of_card_four_local ctx hcard).1
  have hterminalNeighbor : path.a' ∈ neighborhood graph path.firstStep := by
    apply (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
    have hstep := path.path_adj ⟨1, by omega⟩
    have hlast : (⟨1, by omega⟩ : Fin path.length).succ =
        ⟨path.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hlast, path.path_end] at hstep
    simpa only [Fin.castSucc_mk, path.path_first] using hstep
  have hterminalV : z graph path.a' ≤ v graph path.firstStep := by
    rw [v, graph.vAt_def]
    exact le_sSup ⟨path.a', hterminalNeighbor, rfl⟩
  have hnot : ¬ v graph path.firstStep ≤ q graph path.a := by
    intro hle
    have hfirst : path.firstStep ∈ neighborhood graph path.a :=
      (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
    have hcentral : z graph path.a ≤ Subgroup.centralizer (q graph path.a : Set G) :=
      ((lemma_seven_three ctx.sectionSeven graph).center_core path.a path.firstStep hfirst).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))
    exact ctx.commutator_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcentral.trans (Subgroup.centralizer_le (hterminalV.trans hle))))
  apply le_antisymm
  · obtain ⟨outside, houtsideV, houtsideCore⟩ := SetLike.not_le_iff_exists.mp hnot
    intro element helement
    by_cases hcoreElement : element ∈ q graph path.a
    · apply (le_sup_right : Q ≤ v graph path.firstStep ⊔ Q)
      rw [hcore]
      exact ⟨helement.1, hcoreElement⟩
    · have hproduct : outside⁻¹ * element ∈ q graph path.a := by
        apply ((q graph path.a).subgroupOf S).mul_mem_iff_of_index_two hindex
          (a := ⟨outside⁻¹, S.inv_mem (hVS houtsideV)⟩) (b := ⟨element, helement.2⟩) |>.mpr
        simp only [Subgroup.mem_subgroupOf, Subgroup.inv_mem_iff, houtsideCore, hcoreElement]
      have hproductQ : outside⁻¹ * element ∈ Q := by
        rw [hcore]
        exact ⟨L.mul_mem (L.inv_mem (hVL houtsideV)) helement.1, hproduct⟩
      have hmem := (v graph path.firstStep ⊔ Q).mul_mem
        ((le_sup_left : v graph path.firstStep ≤ v graph path.firstStep ⊔ Q) houtsideV)
        ((le_sup_right : Q ≤ v graph path.firstStep ⊔ Q) hproductQ)
      simpa only [mul_inv_cancel_left] using hmem
  · exact sup_le (le_inf hVL hVS) (le_inf (hcore.le.trans inf_le_left) hQS)

end Stellmacher.SectionEight
