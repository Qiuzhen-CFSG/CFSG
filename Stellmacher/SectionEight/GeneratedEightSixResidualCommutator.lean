module

public import Stellmacher.SectionEight.GeneratedEightSixFirstCommutator
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Stellmacher.SectionFiveToSeven.ResidualTwoExtension
public import Stellmacher.SectionEight.GeneratedEightSixInitialCenterResidual

/-!
# The residual commutator in generated Stellmacher (8.6)(1)

The critical terminal center makes the first neighbor-center join escape
the initial core. Lemma (3.4) then puts the initial residual in its local
conjugate closure. Normality of the prescribed intersection propagates the
first commutator bound through that closure, giving the upper bound by the
initial center. Lemma (7.6), through the previous-closure containment, and
residual idempotence identify the closure's residual with the initial residual.
Critical minimality puts the initial center in the intersection; its proved
residual action supplies the reverse containment.

The target is `[D,O²(L)] = Z_a`, not a commutator with `O₂(L)`. This is the
superscript printed in equation (1), p.41 / PDF31 of
`refs/files/stellmacher-n-group.pdf`. Hypothesis Two stays on the ambient
group, through the generated context's graph-preserving local adapter.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement

universe u

public theorem eight_six_residual_mono
    {G : Type u} [Group G] [Finite G]
    (smaller larger : Subgroup G) (hle : smaller ≤ larger) :
    twoResidualIn smaller ≤ twoResidualIn larger := by
  let residual := BenderSuzuki.External.hktPResidual 2 larger
  let _ : residual.Normal := BenderSuzuki.External.hktPResidual_normal
  let projection := (QuotientGroup.mk' residual).comp (Subgroup.inclusion hle)
  have hquotient : IsPGroup 2 (smaller ⧸ projection.ker) :=
    ((BenderSuzuki.External.hktPResidual_quotient_isPGroup
      (q := 2) (Q := larger)).to_subgroup projection.range).of_equiv
        (QuotientGroup.quotientKerEquivRange projection).symm
  have hkernel : twoResidualSubgroup smaller ≤ projection.ker := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_le projection.ker inferInstance hquotient
  rintro element ⟨member, hmember, rfl⟩
  have himage : Subgroup.inclusion hle member ∈ residual :=
    (QuotientGroup.eq_one_iff _).mp (hkernel hmember)
  change _ ∈ (twoResidualSubgroup larger).map larger.subtype
  rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
  exact Subgroup.mem_map_of_mem larger.subtype himage

public theorem eight_six_commutator_conjugate_closure_le
    {G : Type u} [Group G] (fixed seed actors bound : Subgroup G)
    (hseed : seed ≤ actors)
    (hfixed : actors ≤ Subgroup.normalizer fixed)
    (hbound : actors ≤ Subgroup.normalizer bound)
    (hcomm : ⁅fixed, seed⁆ ≤ bound) :
    ⁅fixed, conjugateClosure seed actors⁆ ≤ bound := by
  have hconjBound := Subgroup.le_normalizer_iff.mp hbound
  have hconjFixed := Subgroup.le_normalizer_iff.mp hfixed
  have hprop : ∀ element ∈ conjugateClosure seed actors,
      element ∈ actors ∧ ∀ member ∈ fixed, ⁅member, element⁆ ∈ bound := by
    intro element helement
    induction helement using Subgroup.closure_induction with
    | mem element helement =>
      obtain ⟨actor, generator, rfl⟩ := helement
      refine ⟨actors.mul_mem (actors.mul_mem actor.property
        (hseed generator.property)) (actors.inv_mem actor.property), ?_⟩
      intro member hmember
      have hbase : ⁅(actor : G)⁻¹ * member * actor, (generator : G)⁆ ∈ bound :=
        hcomm (Subgroup.commutator_mem_commutator
          (by simpa using (hconjFixed (actor : G)⁻¹ (actors.inv_mem actor.property)
            member hmember)) generator.property)
      have heq : ⁅member, (actor : G) * generator * (actor : G)⁻¹⁆ =
          (actor : G) * ⁅(actor : G)⁻¹ * member * actor, (generator : G)⁆ *
            (actor : G)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact hconjBound actor actor.property _ hbase
    | one => simp
    | mul left right hleft hright ihleft ihright =>
      refine ⟨actors.mul_mem ihleft.1 ihright.1, ?_⟩
      intro member hmember
      rw [commutatorElement_mul_right_eq_mul_conj]
      simpa only [mul_assoc] using bound.mul_mem (ihleft.2 member hmember)
        (hconjBound left ihleft.1 _ (ihright.2 member hmember))
    | inv element helement ih =>
      refine ⟨actors.inv_mem ih.1, ?_⟩
      intro member hmember
      rw [commutatorElement_inv_right, ← commutatorElement_inv]
      simpa using hconjBound element⁻¹ (actors.inv_mem ih.1) _
        (bound.inv_mem (ih.2 member hmember))
  exact Subgroup.commutator_le.mpr fun member hmember element helement =>
    (hprop element helement).2 member hmember

public theorem eight_six_initial_residual_le_first_join_closure_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2) :
    EAt ctx.Γ ctx.criticalPath.a ≤
      conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep)
        (GAt ctx.Γ ctx.criticalPath.a) := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  have hlength' : path.length = 2 := hlength
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
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
    have hcentral : z graph path.a ≤ Subgroup.centralizer (q graph path.a : Set G) :=
      ((lemma_seven_three ctx.sectionSeven graph).center_core path.a
        path.firstStep hfirst).trans
          ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
            (SevenSix.centerAmbient_le_centralizer _))
    exact ctx.commutator_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcentral.trans (Subgroup.centralizer_le (hterminalV.trans hle))))
  have hVS : v graph path.firstStep ≤ S :=
    (SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) _).trans
      (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path).2
  have hnormal : ((v graph path.firstStep).subgroupOf S).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((SevenSix.edge_sylow_data ctx.sectionSeven graph path).2.1.trans
        (stabilizer_le_normalizer_v graph path.firstStep))
  have hthree := SectionThree.lemma_three_four S
    (SevenSix.sectionThreeHypotheses ctx.sectionSeven) (stabilizer graph path.a)
    ((pFamily_iff_pSet (⊤ : Subgroup G) S _).mp
      (SevenSix.edge_local_data ctx.sectionSeven graph path).1.1)
    (v graph path.firstStep) ⟨hVS, hnormal⟩
    (SevenSix.edge_local_data ctx.sectionSeven graph path).1.2
  have hcomm : ⁅e graph path.a, v graph path.firstStep⁆ = e graph path.a := by
    rcases hthree with hcore | hcomm
    · apply (hnot ?_).elim
      change v graph path.firstStep ≤ graph.twoCoreAt path.a
      rw [graph.twoCoreAt_def]
      exact hcore
    · simpa only [CosetGraphContext.e, graph.twoResidualAt_def, twoResidualIn,
        stabilizer] using hcomm
  change e graph path.a ≤ _
  rw [← hcomm]
  exact SevenSix.commutator_le_conjugateClosure _ _ _
    (by simpa only [CosetGraphContext.e, graph.twoResidualAt_def, stabilizer, GAt] using
      SevenSix.twoResidualIn_le (stabilizer graph path.a))

public theorem eight_six_residual_commutator_le_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a)
    (D L : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hnormal : NormalIn D (GAt ctx.Γ ctx.criticalPath.a))
    (hfirst : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅D, twoResidualIn L⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a := by
  have hclosure := eight_six_previous_closure_containments
    ctx.sectionSeven ctx.Γ ctx.criticalPath previous hprevious
  rw [← hL] at hclosure
  have hresidual : twoResidualIn L ≤ EAt ctx.Γ ctx.criticalPath.a := by
    rw [EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact eight_six_residual_mono _ _ hclosure.1
  have hVS : VAt ctx.Γ ctx.criticalPath.firstStep ≤ S :=
    (SevenSix.neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
      (by omega) _).trans
        (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hbound : ⁅D, VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a := by
    rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono le_rfl (hD.le.trans inf_le_right)).trans
      hfirst.le).trans (eight_six_first_step_fixed_line_local ctx hcenter hcard).2
  exact (Subgroup.commutator_mono le_rfl (hresidual.trans
    (eight_six_initial_residual_le_first_join_closure_local ctx hlength))).trans
      (eight_six_commutator_conjugate_closure_le _ _ _ _
        (hVS.trans (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2)
        (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a) hbound)

public theorem eight_six_residual_eq_initial_of_closure
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex)
    (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (L : Subgroup G)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a)) :
    twoResidualIn L = EAt graph path.a := by
  have hclosure := eight_six_previous_closure_containments hyp graph path previous hprevious
  rw [← hL] at hclosure
  have hidempotent : twoResidualIn (EAt graph path.a) = EAt graph path.a := by
    rw [EAt, CosetGraphContext.e, graph.twoResidualAt_def]
    change twoResidualAmbient (twoResidualAmbient _) = twoResidualAmbient _
    rw [twoResidualAmbient, SectionThree.twoResidualSubgroup_eq_hktPResidual',
      twoResidualAmbient_has_top_twoResidual, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  apply le_antisymm
  · rw [EAt, CosetGraphContext.e, graph.twoResidualAt_def]
    exact eight_six_residual_mono _ _ hclosure.1
  · rw [← hidempotent]
    exact eight_six_residual_mono _ _ hclosure.2

public theorem eight_six_initial_center_le_intersection_of_length_two
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : path.length = 2)
    (previous : graph.Vertex)
    (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (D : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep) :
    ZAt graph path.a ≤ D := by
  have hcenterNeighbor : ∀ neighbor ∈ neighborhood graph path.a,
      z graph path.a ≤ q graph neighbor := by
    intro neighbor hneighbor
    have hback : path.a ∈ neighborhood graph neighbor :=
      (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
        (graph.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hneighbor))
    have hcenterV : z graph path.a ≤ v graph neighbor := by
      rw [v, graph.vAt_def]
      exact le_sSup ⟨path.a, hback, rfl⟩
    exact hcenterV.trans
      (SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) neighbor)
  rw [hD]
  exact le_inf (hcenterNeighbor previous hprevious)
    (hcenterNeighbor path.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj))

public theorem generated_eight_six_residual_commutator
    {H : Type u} [Group H] [Finite H] {S0 : Sylow 2 H}
    {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (_hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (_hQ : Q = twoCoreIn L)
    (hnormal : NormalIn D (GAt ctx.Γ ctx.criticalPath.a))
    (_hsylow : L ⊓ S.subgroupOf (P1 ⊔ P2) = VAt ctx.Γ ctx.criticalPath.firstStep ⊔ Q)
    (hfirst : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅D, twoResidualIn L⁆ = ZAt ctx.Γ ctx.criticalPath.a := by
  apply le_antisymm
  · exact eight_six_residual_commutator_le_local ctx.toLocalContext hcenter hlength hcard
      previous hprev.1 D L hD hL hnormal hfirst
  · have hcenterD := eight_six_initial_center_le_intersection_of_length_two
      ctx.Γ ctx.criticalPath hlength previous hprev.1 D hD
    have hresidual := eight_six_residual_eq_initial_of_closure ctx.sectionSeven
      ctx.Γ ctx.criticalPath previous hprev.1 L hL
    have haction : ⁅ZAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆ =
        ZAt ctx.Γ ctx.criticalPath.a :=
      eight_six_initial_center_residual_local ctx.toLocalContext hcenter hcard
    rw [hresidual, ← haction]
    exact Subgroup.commutator_mono hcenterD le_rfl

end Stellmacher.SectionEight
