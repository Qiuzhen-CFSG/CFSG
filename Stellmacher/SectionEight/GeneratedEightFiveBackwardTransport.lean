module

public import Stellmacher.SectionEight.GeneratedEightFiveBackwardModuleControl
public import Stellmacher.SectionThree.LemmaThreeSeven
public import Stellmacher.SectionTwo.NestedSL2OutsideGeneration

/-! # Local BackwardTransport for generated Stellmacher (8.5)

The Section Seven hypotheses belong to the graph group. No Hypothesis Two
is imposed on that group. Source: printed pp.40–41, proof of (8.5).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

private theorem frattini_eq_bot_of_card_six
    {group : Type*} [Group group] [Finite group] (hcard : Nat.card group = 6) :
    frattini group = ⊥ := by
  classical
  let twoSylow : Sylow 2 group := default
  let threeSylow : Sylow 3 group := default
  have hfactorTwo : Nat.factorization 6 2 = 1 := by
    change Nat.factorization (3 * 2) 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hfactorThree : Nat.factorization 6 3 = 1 := by
    change Nat.factorization (3 * 2) 3 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have htwo : Nat.card twoSylow = 2 := by
    rw [twoSylow.card_eq_multiplicity, hcard, hfactorTwo]
    norm_num
  have hthree : Nat.card threeSylow = 3 := by
    rw [threeSylow.card_eq_multiplicity, hcard, hfactorThree]
    norm_num
  have hmaximal : ∀ subgroup : Subgroup group,
      Nat.card subgroup = 2 ∨ Nat.card subgroup = 3 → IsCoatom subgroup := by
    intro subgroup hsubcard
    constructor
    · intro htop
      have hsize := congrArg (fun member : Subgroup group => Nat.card member) htop
      simp only [Subgroup.card_top, hcard] at hsize
      omega
    · intro larger hlarge
      have hdiv := Subgroup.card_dvd_of_le hlarge.le
      have hdivSix : Nat.card larger ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card larger
      have hbound : Nat.card larger ≤ 6 := Nat.le_of_dvd (by omega) hdivSix
      have hstrict : Nat.card subgroup < Nat.card larger := by
        apply lt_of_le_of_ne (Subgroup.card_le_of_le hlarge.le)
        intro heq
        exact hlarge.ne (Subgroup.eq_of_le_of_card_ge hlarge.le heq.symm.le)
      apply Subgroup.eq_top_of_card_eq
      rw [hcard]
      rcases hsubcard with hsubcard | hsubcard <;>
        rw [hsubcard] at hstrict hdiv <;>
        interval_cases hsize : Nat.card larger <;> norm_num [hsize] at *
  have hdisjoint : Disjoint (twoSylow : Subgroup group) (threeSylow : Subgroup group) :=
    Subgroup.disjoint_of_coprime_natCard (by rw [htwo, hthree]; decide)
  apply bot_unique
  rw [← hdisjoint.eq_bot]
  exact le_inf (frattini_le_coatom (hmaximal _ (Or.inl htwo)))
    (frattini_le_coatom (hmaximal _ (Or.inr hthree)))

private theorem exists_generating_backward_neighbor
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquotient : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : 1 < ctx.criticalPath.length) :
    ∃ backward : ctx.Γ.Vertex,
      backward ∈ neighborhood ctx.Γ ctx.criticalPath.a ∧
      backward ≠ ctx.criticalPath.firstStep ∧
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ backward) ⊔
        ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a := by
  classical
  let graph := ctx.Γ
  let path := ctx.criticalPath
  have hlen : 1 < path.length := hlength
  let localGroup := stabilizer graph path.a
  let opposite := (z graph path.a').subgroupOf localGroup
  have hyp := ctx.sectionSeven
  have hfour := lemma_seven_four hyp graph path
  have hlocal := (SevenSix.edge_local_data hyp graph path).1
  have hcenterLe : z graph path.a' ≤ localGroup := hfour.reverse_containment.1
  have hcenterOutside : ¬ z graph path.a' ≤ q graph path.a :=
    (hfour.commutator_case ctx.commutator_ne).2.2
  have hcoreNontrivial : pCore 2 localGroup ≠ ⊥ := by
    intro hbot
    apply hlocal.1.1.2.2.1
    change twoCoreIn localGroup = ⊥
    simp [twoCoreIn, hbot]
  have hlast : path.path ⟨path.length - 1, by omega⟩ ∈ neighborhood graph path.a' := by
    apply (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
    have hadj := path.path_adj ⟨path.length - 1, by omega⟩
    have hindex : (⟨path.length - 1, by omega⟩ : Fin path.length).succ =
        ⟨path.length, Nat.lt_succ_self _⟩ := by apply Fin.ext; simp; omega
    rw [hindex, path.path_end] at hadj
    exact graph.adjacent_symm hadj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor hyp graph hlast
  have hopposite : IsPGroup 2 opposite :=
    (IsElementaryAbelian.isPGroup 2 (z graph path.a')).comap_of_injective
      localGroup.subtype localGroup.subtype_injective
  have houtside : ¬ opposite ≤ pCore 2 localGroup := by
    intro hle
    apply hcenterOutside
    have hmap := Subgroup.map_mono (f := localGroup.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hcenterLe] at hmap
    change z graph path.a' ≤ graph.twoCoreAt path.a
    rw [graph.twoCoreAt_def]
    exact hmap
  have hnative : IsSL2Two (localGroup ⧸ pCore 2 localGroup) := by
    obtain ⟨projection, hsurjective, hkernel⟩ := hquotient
    have hker : projection.ker = pCore 2 localGroup := by
      rw [hkernel]
      change (graph.twoCoreAt path.a).subgroupOf localGroup = _
      rw [graph.twoCoreAt_def, twoCoreIn]
      exact subgroupOf_map_subtype_eq (pCore 2 localGroup)
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective projection hsurjective)⟩
  have hnested : IsSL2Two
      ((localGroup ⧸ pCore 2 localGroup) ⧸ frattini (localGroup ⧸ pCore 2 localGroup)) := by
    have hcard := SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hnative
    obtain ⟨equiv⟩ := hnative
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (frattini_eq_bot_of_card_six hcard)).trans
      (QuotientGroup.quotientBot.trans equiv)⟩
  obtain ⟨chosenSylow, hgenerate⟩ :=
    SectionTwo.exists_sylow_sup_eq_top_of_outside_nestedSL2Two
      hlocal.2 hcoreNontrivial opposite hopposite houtside hnested
  obtain ⟨_, edgeSylow, hedge⟩ := hlocal.1.1.2.1
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq localGroup edgeSylow chosenSylow
  let backward := graph.act ((actor : G)⁻¹) path.firstStep
  have hfix : graph.act ((actor : G)⁻¹) path.a = path.a := by
    have hmem : (actor : G)⁻¹ ∈ stabilizer graph path.a := localGroup.inv_mem actor.property
    exact Set.ext_iff.mp (graph.stabilizer_def path.a) _ |>.mp hmem
  have hbackward : backward ∈ neighborhood graph path.a := by
    apply (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
    have hadj := adjacent_act graph ((actor : G)⁻¹) path.firstStep_adj
    rwa [hfix] at hadj
  have hchosen : (chosenSylow : Subgroup localGroup).map localGroup.subtype ≤
      stabilizer graph backward := by
    rw [show backward = graph.act ((actor : G)⁻¹) path.firstStep from rfl,
      stabilizer_act, inv_inv]
    change (chosenSylow : Subgroup localGroup).map localGroup.subtype ≤
      (stabilizer graph path.firstStep).map (MulAut.conj (actor : G)).toMonoidHom
    have hmap : (chosenSylow : Subgroup localGroup).map localGroup.subtype =
        S.map (MulAut.conj (actor : G)).toMonoidHom := by
      rw [← hactor]
      change ((edgeSylow : Subgroup localGroup).map
        (MulAut.conj actor).toMonoidHom).map localGroup.subtype = _
      calc
        _ = ((edgeSylow : Subgroup localGroup).map localGroup.subtype).map
            (MulAut.conj (actor : G)).toMonoidHom := by
          rw [Subgroup.map_map, Subgroup.map_map]
          rfl
        _ = _ := congrArg (Subgroup.map (MulAut.conj (actor : G)).toMonoidHom) hedge
    rw [hmap]
    exact Subgroup.map_mono (path.S_le_edge_stabilizers.trans inf_le_right)
  have hgenerateAmbient : z graph path.a' ⊔
      (chosenSylow : Subgroup localGroup).map localGroup.subtype = localGroup := by
    have hmap := congrArg (Subgroup.map localGroup.subtype) hgenerate
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hcenterLe,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hmap
  have hjoin : (stabilizer graph path.a ⊓ stabilizer graph backward) ⊔
      z graph path.a' = stabilizer graph path.a := by
    apply le_antisymm (sup_le inf_le_left hcenterLe)
    change localGroup ≤ _
    conv_lhs => rw [← hgenerateAmbient]
    exact sup_le le_sup_right
      ((le_inf (Subgroup.map_subtype_le _) hchosen).trans le_sup_left)
  refine ⟨backward, hbackward, ?_, hjoin⟩
  intro hequal
  have hterminalCore : z graph path.a' ≤ q graph path.firstStep := by
    apply SevenSix.critical_minimality graph path
    have hdist := SevenSix.path_distance_le graph path 1 path.length (by omega) le_rfl
    rw [path.path_first, path.path_end, graph.distance_symm] at hdist
    exact hdist.trans_lt (by omega)
  have hterminalLe : z graph path.a' ≤ stabilizer graph path.firstStep := by
    change z graph path.a' ≤ graph.vertexStabilizer path.firstStep
    exact hterminalCore.trans (by
      rw [q, graph.twoCoreAt_def]
      exact SevenSix.twoCoreIn_le _)
  have hlocalLe : stabilizer graph path.a ≤ stabilizer graph path.firstStep := by
    rw [← hjoin, hequal]
    exact sup_le inf_le_right hterminalLe
  have hcores : twoCoreIn (P1 ⊔ P2) = ⊥ := by
    rw [hyp.generated, twoCoreIn]
    have hcoreTop : pCore 2 (⊤ : Subgroup G) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective
        (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) _
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).injective).mp
      rw [pCore_map_iso, hyp.twoCore_eq_bot]
    rw [hcoreTop, Subgroup.map_bot]
  have hnontrivial := (SevenSix.edge_local_data hyp graph path).2.1.1.2.2.1
  apply hnontrivial
  rcases path.edge_stabilizers_are_P with hedge | hedge
  · rw [hedge.1, hedge.2] at hlocalLe
    rw [sup_eq_right.mpr hlocalLe] at hcores
    rwa [hedge.2]
  · rw [hedge.1, hedge.2] at hlocalLe
    rw [sup_eq_left.mpr hlocalLe] at hcores
    rwa [hedge.2]

open scoped commutatorElement

private theorem map_module_le_acted_module
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (actor : G) (vertex : graph.Vertex) :
    (v graph vertex).map (MulAut.conj actor⁻¹).toMonoidHom ≤
      v graph (graph.act actor vertex) := by
  rw [v, graph.vAt_def, sSup_eq_iSup, Subgroup.map_iSup]
  apply iSup_le
  intro center
  rw [Subgroup.map_iSup]
  apply iSup_le
  rintro ⟨neighbor, hneighbor, rfl⟩
  change (z graph neighbor).map (MulAut.conj actor⁻¹).toMonoidHom ≤ _
  rw [← z_act]
  rw [v, graph.vAt_def]
  apply le_sSup
  refine ⟨graph.act actor neighbor, ?_, rfl⟩
  apply (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
  exact adjacent_act graph actor
    ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hneighbor)

private theorem module_transport_of_core_containment
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (backward second : graph.Vertex)
    (hbackward : backward ∈ neighborhood graph path.a)
    (hsecond : second ∈ neighborhood graph path.firstStep)
    (hcore : v graph backward ≤ q graph path.firstStep) :
    ∃ transported : graph.Vertex,
      transported ∈ neighborhood graph second ∧
      v graph backward ≤ v graph transported ⊔ twoCoreIn (e graph path.firstStep) := by
  classical
  let localGroup := stabilizer graph path.firstStep
  let residual := twoResidualIn localGroup
  have hresidual : residual = e graph path.firstStep :=
    (graph.twoResidualAt_def path.firstStep).symm
  have hSP : S ≤ localGroup := path.S_le_edge_stabilizers.trans inf_le_right
  have hEP : residual ≤ localGroup := SevenSix.twoResidualIn_le localGroup
  let nativeResidual := residual.subgroupOf localGroup
  let nativeSylow := S.subgroupOf localGroup
  let _ : nativeResidual.Normal := SevenSix.twoResidualIn_normal localGroup
  have hgenerate : nativeSylow ⊔ nativeResidual = ⊤ := by
    apply Subgroup.map_injective localGroup.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSP,
      Subgroup.map_subgroupOf_eq_of_le hEP, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, sup_comm]
    exact SectionThree.twoResidual_sup_sylowImage
      (SevenSix.edge_local_data hyp graph path).2.1.1.2.1.2
  have hstart : path.a ∈ neighborhood graph path.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm path.firstStep_adj)
  obtain ⟨actor, hactor⟩ := (lemma_seven_one hyp graph).local_transitivity
    path.firstStep hstart hsecond
  have hmem : actor ∈ nativeSylow ⊔ nativeResidual := by rw [hgenerate]; trivial
  obtain ⟨sylowActor, hsylow, residualActor, hres, hproduct⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hmem
  have hfix : graph.act (sylowActor : G) path.a = path.a := by
    have hfixmem := path.S_le_edge_stabilizers.trans inf_le_left hsylow
    exact Set.ext_iff.mp (graph.stabilizer_def path.a) _ |>.mp hfixmem
  have hmove : graph.act (residualActor : G) path.a = second := by
    rw [← hproduct] at hactor
    change graph.act ((sylowActor : G) * (residualActor : G)) path.a = second at hactor
    rwa [graph.act_mul, hfix] at hactor
  let transported := graph.act (residualActor : G) backward
  refine ⟨transported, ?_, ?_⟩
  · apply (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
    have hadj := adjacent_act graph (residualActor : G)
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hbackward)
    rwa [hmove] at hadj
  · intro element helement
    have hconjugate : (residualActor : G)⁻¹ * element * (residualActor : G) ∈
        v graph transported := by
      apply map_module_le_acted_module graph (residualActor : G) backward
      exact ⟨element, helement, by simp [mul_assoc]⟩
    have hcomm : ⁅(residualActor : G)⁻¹, element⁆ ∈ twoCoreIn residual := by
      apply SevenSix.residual_commutator_core_le localGroup
      apply Subgroup.commutator_mem_commutator (residual.inv_mem hres)
      exact graph.twoCoreAt_def path.firstStep ▸ hcore helement
    have hleft : ⁅(residualActor : G)⁻¹, element⁆ ∈
        v graph transported ⊔ twoCoreIn (e graph path.firstStep) :=
      Subgroup.mem_sup_right (hresidual ▸ hcomm)
    have hright : (residualActor : G)⁻¹ * element * (residualActor : G) ∈
        v graph transported ⊔ twoCoreIn (e graph path.firstStep) :=
      Subgroup.mem_sup_left hconjugate
    have hresult := (v graph transported ⊔ twoCoreIn (e graph path.firstStep)).mul_mem
      ((v graph transported ⊔ twoCoreIn (e graph path.firstStep)).inv_mem hleft) hright
    simpa [commutatorElement_def, mul_assoc] using hresult

public theorem eight_five_backward_transport_local
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hquotient : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : 2 < ctx.criticalPath.length)
    (hfirst : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hlast : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩)) :
    ∃ backward transported : ctx.Γ.Vertex,
      backward ∈ neighborhood ctx.Γ ctx.criticalPath.a ∧
      backward ≠ ctx.criticalPath.firstStep ∧
      transported ∈ neighborhood ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩) ∧
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ backward) ⊔
        ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a ∧
      VAt ctx.Γ backward ≤ VAt ctx.Γ transported ⊔
        twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ∧
      (VAt ctx.Γ backward ≤ GAt ctx.Γ ctx.criticalPath.a' →
        ⁅ZAt ctx.Γ ctx.criticalPath.a', VAt ctx.Γ backward⁆ ≤
          ZAt ctx.Γ ctx.criticalPath.a) := by
  have control := eight_five_backward_module_control_local ctx hcenter hfour hquotient
    hlength hfirst hlast
  obtain ⟨backward, hbackward, hdistinct, hgenerate⟩ :=
    exists_generating_backward_neighbor ctx hquotient (by omega)
  obtain ⟨hcore, hcommutator⟩ := control backward hbackward hdistinct hgenerate
  have hsecond : ctx.criticalPath.path ⟨2, by omega⟩ ∈
      neighborhood ctx.Γ ctx.criticalPath.firstStep := by
    apply (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr
    have hadj := ctx.criticalPath.path_adj ⟨1, by omega⟩
    simpa [ctx.criticalPath.path_first] using hadj
  obtain ⟨transported, htransported, hbound⟩ :=
    module_transport_of_core_containment
      (ctx.sectionSeven)
      ctx.Γ ctx.criticalPath backward _ hbackward hsecond hcore
  exact ⟨backward, transported, hbackward, hdistinct, htransported,
    hgenerate, hbound, hcommutator⟩

end Stellmacher.SectionEight
