module
public import Stellmacher.SectionTen.TenOneLargeTerminalCoreFixed
public import Stellmacher.SectionTen.TenOneLargeFirstCentralizerAction
public import Stellmacher.SectionTen.TenOneFiveResidualSmallCommutator
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer
public import Stellmacher.SectionTen.TenOneLargeFirstIrreducible
public import Theory.GroupAction.QuotientCommutatorFamily
public import Stellmacher.SectionTen.TenOneLargeResidualCentralizerFinal
/-!
# The terminal residual-core centralizer in the five-residual case

In the actual large Section Ten configuration, the centralizer of
O₂(E_terminal) inside Q_terminal is exactly Z_terminal. The theorem retains
the original no-transvection hypothesis and the genuine first residual
quotient model C₅. No exponent or commutativity condition on this centralizer,
no containment in the generated neighborhood, and no later core-index bound
is assumed.

Write C for that centralizer. The generated subgroup and terminal fixed-line
results put C in Q_middle and identify its intersections with both endpoint
modules as Z_terminal. The five-residual small-commutator obstruction then
puts C in the first module centralizer. The first residual acts on C modulo
the first module; the middle coatom commutator lies in Z_terminal.

The first stabilizer normalizes C joined with V_first: its edge is generated
by Q_middle and O₂(E_first), and the actual edge Sylow supplements E_first.
The quotient commutator pairing for this join centralizes V_first and has
individual images of order at most four in V_first/Z_first, of order sixteen.
Irreducibility for the same literal first quotient action makes all images
trivial. Thus [C,O₂(E_first)] lies in Z_first, and its middle coatom commutes
with C because the two endpoint center lines are disjoint.

The imported final native transfer normalizes C Z_middle. Its middle-core
commutator and its square-generated subgroup are middle-normal and lie in C;
actual residual generation (7.6) and the residual-centralizer conclusion
(7.5)(c) kill both. Hence C lies in Z_middle, where the already identified
module intersection gives C=Z_terminal.

Source: Stellmacher (10.1)(20), Journal of Algebra 190 (1997), printed p.65.
The final transfer uses genuine E_middle-centralization before (7.5)(c);
it does not silently replace that residual by its two-core.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem residual_core_centralizer_setup
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hfive : Nonempty (((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep))) ≃* C5)) :
    let C:=QAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') : Set G)
    C≤QAt ctx.Γ middle ∧
    GAt ctx.Γ ctx.criticalPath.a'≤Subgroup.normalizer (C:Set G) ∧
    C≤QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep:Set G) ∧
    C⊓VAt ctx.Γ ctx.criticalPath.firstStep=ZAt ctx.Γ ctx.criticalPath.a' ∧
    C⊓VAt ctx.Γ ctx.criticalPath.a'=ZAt ctx.Γ ctx.criticalPath.a' ∧
    ⁅C,EAt ctx.Γ ctx.criticalPath.firstStep⁆≤VAt ctx.Γ ctx.criticalPath.firstStep ∧
    ⁅C,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⊓QAt ctx.Γ middle⁆≤
      ZAt ctx.Γ ctx.criticalPath.a' := by
  dsimp only
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let Q:=QAt ctx.Γ ctx.criticalPath.a'
  let C:=Q⊓Subgroup.centralizer (U:Set G)
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let M:=GAt ctx.Γ middle
  let Qm:=QAt ctx.Γ middle
  let W:=conjugateClosure (A⊓Q) M
  let O:=omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)
  let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔O
  obtain ⟨horbit,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hlong : 2<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hE : E=twoResidualIn P:=ctx.Γ.twoResidualAt_def _
  have hEP : E≤P:=hE ▸ twoResidualIn_le P
  have hUP : U≤P:=(twoCoreIn_le E).trans hEP
  have hPU : P≤Subgroup.normalizer (U:Set G):=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPC : P≤Subgroup.normalizer (C:Set G):=
    (le_inf (stabilizer_le_normalizer_q ctx.Γ _) (hPU.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQM : Q≤M:=((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2
  have hQmP : Qm≤P:=((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal) default).2.2
  have hQmFirst : Qm≤GAt ctx.Γ ctx.criticalPath.firstStep:=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2
  have hVQ : V≤Q:=neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort _
  have hVU : V≤U:=by
    have hfull : ⁅V,E⁆=V:=ten_one_large_terminal_residual_full ctx middle hpath hno
    rw [←hfull]
    apply (Subgroup.commutator_mono hVQ le_rfl).trans
    rw [Subgroup.commutator_comm]
    change ⁅E,ctx.Γ.twoCoreAt ctx.criticalPath.a'⁆≤twoCoreIn E
    rw [hE,ctx.Γ.twoCoreAt_def]
    exact residual_commutator_core_le P
  have hCV : C≤Subgroup.centralizer (V:Set G):=
    inf_le_right.trans (Subgroup.centralizer_le hVU)
  have hfixed : V⊓Subgroup.centralizer (U:Set G)=Z:=
    ten_one_large_terminal_core_fixed_line ctx middle hpath hno
  have hZC : Z≤C:=hfixed.symm.le.trans (inf_le_inf_right _ hVQ)
  have hCinfV : C⊓V=Z:=by
    apply le_antisymm
    · exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans_eq hfixed
    · exact le_inf hZC (hfixed.symm.le.trans inf_le_left)
  have hmidI : ZAt ctx.Γ middle≤A⊓V:=le_inf
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst))
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))
  have hmidW : ZAt ctx.Γ middle≤W:=hmidI.trans (ten_one_common_intersection_le_generated ctx middle)
  have hWU : W≤U:=(ten_one_large_first_residual_index ctx middle hpath hno).2
  have hC2 : IsPGroup 2 C:=by
    exact nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ _ C inf_le_left
  have hCQm : C≤Qm:=nine_three_orbit_pgroup_centralizer
    ctx.toLocalContext.toSectionNineLocalContext middle horbit C hC2
    (inf_le_left.trans hQM)
    (inf_le_right.trans (Subgroup.centralizer_le (hmidW.trans hWU)))
  obtain ⟨hsplit,hDO,_,_,_⟩:=ten_one_large_omega_fixed_component ctx middle hpath hno
  have hOV : O≤V:=(ten_one_large_neighborhood_omega_center ctx middle hpath hno).le.trans inf_le_right
  have hBV : Y⊔V≤V:=hsplit.le.trans (sup_le le_rfl (hDO.trans hOV))
  have hCWV : W⊓Subgroup.centralizer (V:Set G)≤V:=
    (le_sup_left.trans le_sup_left).trans hBV
  have hCinfA : C⊓A=Z:=by
    apply le_antisymm
    · have hCAW : C⊓A≤W:=by
        intro x hx
        apply Subgroup.subset_closure
        refine ⟨(1:M),⟨x,hx.2,hx.1.1⟩,?_⟩
        simp
      have hCAV : C⊓A≤V:=(le_inf hCAW (inf_le_left.trans hCV)).trans hCWV
      exact (le_inf inf_le_left hCAV).trans_eq hCinfV
    · exact le_inf hZC ((show Z≤ZAt ctx.Γ middle by
        rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
        exact le_sup_right).trans (hmidI.trans inf_le_left))
  have hAQm : A≤Qm:=(show A≤GeneratedNeighborhoodV ctx.Γ middle from le_sSup
    ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,rfl⟩).trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hlong middle)
  have hCA : ⁅C,A⁆≤Z:=by
    exact (le_inf
      (Subgroup.le_normalizer_iff_commutator_le_left.mp ((hAQm.trans hQmP).trans hPC))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((hCQm.trans hQmFirst).trans (stabilizer_le_normalizer_v ctx.Γ _)))).trans_eq hCinfA
  have hfirstData:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩
  have hCfirst : C≤QAt ctx.Γ ctx.criticalPath.firstStep⊓Subgroup.centralizer (A:Set G):=by
    intro c hc
    have hcA : c∈Subgroup.centralizer (A:Set G):=
      ten_one_five_residual_small_commutator_centralizes_first ctx middle hpath hfive c
        (hQmFirst (hCQm hc)) (by
          rw [Subgroup.commutator_comm]
          exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hc) le_rfl).trans hCA)
    refine ⟨(hfirstData.2.2 c (hQmFirst (hCQm hc))).mp ?_,hcA⟩
    have hbot : ⁅A,Subgroup.zpowers c⁆=⊥:=by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr hcA)
    rw [hbot]
    exact bot_le
  have hCE : ⁅C,EAt ctx.Γ ctx.criticalPath.firstStep⁆≤A:=
    (Subgroup.commutator_mono hCfirst le_rfl).trans
      (ten_one_large_first_centralizer_residual_commutator ctx middle hpath hno)
  have hCK : ⁅C,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⊓Qm⁆≤Z:=by
    apply (le_inf ?_ ?_).trans_eq hCinfA
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((inf_le_right.trans hQmP).trans hPC)
    · exact (Subgroup.commutator_mono le_rfl (inf_le_left.trans (twoCoreIn_le _))).trans hCE
  exact ⟨hCQm,hPC,hCfirst,hCinfA,hCinfV,hCE,hCK⟩


private theorem first_core_edge
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    GAt ctx.Γ middle⊓GAt ctx.Γ ctx.criticalPath.firstStep=
      QAt ctx.Γ middle⊔twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ∧
    (QAt ctx.Γ middle).relIndex (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep))=2 := by
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let M:=GAt ctx.Γ middle
  let Q:=QAt ctx.Γ middle
  let E:=EAt ctx.Γ ctx.criticalPath.firstStep
  let U:=twoCoreIn E
  let edge:=M⊓P
  obtain ⟨_,hfirst,_,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hUQ : U≤QAt ctx.Γ ctx.criticalPath.firstStep:=by
    change twoCoreIn (ctx.Γ.twoResidualAt _)≤ctx.Γ.twoCoreAt _
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hEP : E≤P:=by
    change ctx.Γ.twoResidualAt _≤P
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hUP : U≤P:=(twoCoreIn_le E).trans hEP
  have hUm : U≤M:=hUQ.trans (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst)) default).2.2)
  have hQm : Q≤M:=by
    change ctx.Γ.twoCoreAt middle≤M
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQP : Q≤P:=((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2
  have hQedge : Q≤edge:=le_inf hQm hQP
  have hUedge : U≤edge:=le_inf hUm hUP
  have hescape : ¬U≤Q:=nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.firstStep middle
      ⟨1,ctx.Γ.act_one _⟩ (ctx.Γ.adjacent_symm hfirst)
  have hcard : Nat.card edge=2*Nat.card Q:=
    (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
      (sectionTenOpeningData ctx middle hpath).quotient_model).edge_card _ hfirst
  have hQindex : Q.relIndex edge=2:=by
    have hh:=(Q.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQedge).toEquiv] at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hh.trans hcard)
  have hgen : edge=Q⊔U:=by
    have hjoin : Q⊔U≤edge:=sup_le hQedge hUedge
    have hdiv : Q.relIndex (Q⊔U)∣2:=by
      rw [←hQindex]
      exact dvd_of_mul_right_eq ((Q⊔U).relIndex edge)
        (Subgroup.relIndex_mul_relIndex Q (Q⊔U) edge le_sup_left hjoin)
    have hindex : Q.relIndex (Q⊔U)=2:=by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone|htwo
      · exact (hescape (le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone))).elim
      · exact htwo
    have hjoinCard : Nat.card (Q⊔U:Subgroup G)=2*Nat.card Q:=by
      have hh:=(Q.subgroupOf (Q⊔U)).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Q≤Q⊔U from le_sup_left)).toEquiv] at hh
      change Q.relIndex (Q⊔U)*Nat.card Q=Nat.card (Q⊔U:Subgroup G) at hh
      rw [hindex] at hh
      exact hh.symm
    exact (Subgroup.eq_of_le_of_card_ge hjoin (by rw [hjoinCard,hcard])).symm
  refine ⟨hgen,?_⟩
  have hdiv : Q.relIndex U∣2:=by
    let _ : (Q.subgroupOf edge).Normal:=Subgroup.normal_of_index_eq_two hQindex
    rw [←hQindex,←Subgroup.relIndex_subgroupOf hUedge]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone|htwo
  · exact (hescape (Subgroup.relIndex_eq_one.mp hone)).elim
  · exact htwo

private theorem first_normalizes_centralizer_enlargement
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (C : Subgroup G)
    (hCP : C≤GAt ctx.Γ ctx.criticalPath.firstStep)
    (hPC : GAt ctx.Γ ctx.criticalPath.a'≤Subgroup.normalizer (C:Set G))
    (hCE : ⁅C,EAt ctx.Γ ctx.criticalPath.firstStep⁆≤VAt ctx.Γ ctx.criticalPath.firstStep) :
    GAt ctx.Γ ctx.criticalPath.firstStep≤
      Subgroup.normalizer ((C⊔VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G):Set G) ∧
    ⁅C⊔VAt ctx.Γ ctx.criticalPath.firstStep,EAt ctx.Γ ctx.criticalPath.firstStep⁆≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.firstStep
  let E:=EAt ctx.Γ ctx.criticalPath.firstStep
  let U:=twoCoreIn E
  let BB:=C⊔V
  let edge:=P⊓GAt ctx.Γ middle
  obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hEP : E≤P:=by
    change ctx.Γ.twoResidualAt _≤P
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hPV : P≤Subgroup.normalizer (V:Set G):=stabilizer_le_normalizer_v ctx.Γ _
  have hEV : E≤Subgroup.normalizer (V:Set G):=hEP.trans hPV
  have hBE : ⁅BB,E⁆≤V:=by
    have hVP : V≤P:=(neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
      (by rw [ctx.critical_length];decide) _).trans (by
        change ctx.Γ.twoCoreAt _≤P
        rw [ctx.Γ.twoCoreAt_def]
        exact twoCoreIn_le _)
    have hh:=SectionEight.eight_six_commutator_sSup_le ({C,V}:Set (Subgroup G)) E V P hPV
      (by intro D hD;rcases hD with rfl|hD;exact hCP
          have : D=V:=Set.mem_singleton_iff.mp hD;subst D;exact hVP)
      (by intro D hD;rcases hD with rfl|hD;exact hCE
          have : D=V:=Set.mem_singleton_iff.mp hD;subst D
          exact Subgroup.le_normalizer_iff_commutator_le_left.mp hEV)
    simpa only [sSup_pair] using hh
  have hEB : E≤Subgroup.normalizer (BB:Set G):=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hBE.trans le_sup_right)
  have hQB : QAt ctx.Γ middle≤Subgroup.normalizer (BB:Set G):=by
    have hQfirst : QAt ctx.Γ middle≤P:=((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2
    have hQend : QAt ctx.Γ middle≤GAt ctx.Γ ctx.criticalPath.a':=
      ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal) default).2.2
    exact (le_inf (hQend.trans hPC) (hQfirst.trans hPV)).trans
      (C.normalizer_inf_normalizer_le_normalizer_sup V)
  have hedgeB : edge≤Subgroup.normalizer (BB:Set G):=by
    have heq : edge=QAt ctx.Γ middle⊔U:=by
      change P⊓GAt ctx.Γ middle=_
      rw [inf_comm]
      exact (first_core_edge ctx middle hpath).1
    rw [heq]
    exact sup_le hQB ((twoCoreIn_le E).trans hEB)
  let edgeSylow : Sylow 2 edge:=default
  have hdata:=edge_sectionThree_data ctx.sectionSeven ctx.Γ
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst)) edgeSylow
  have hgen:=SectionThree.twoResidual_sup_sylowImage hdata.2.1.1.2.1
  have hE : twoResidualAmbient P=E:=by
    change twoResidualAmbient P=ctx.Γ.twoResidualAt _
    rw [ctx.Γ.twoResidualAt_def]
    rfl
  rw [hE] at hgen
  change E⊔sylowTwoAmbient edge edgeSylow=P at hgen
  refine ⟨?_,hBE⟩
  change P≤Subgroup.normalizer (BB:Set G)
  rw [←hgen]
  exact sup_le hEB ((Subgroup.map_subtype_le _).trans hedgeB)


private theorem first_small_images
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (C : Subgroup G) (hCQm : C≤QAt ctx.Γ middle)
    (hCV : C≤Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep:Set G))
    (hBE : ⁅C⊔VAt ctx.Γ ctx.criticalPath.firstStep,EAt ctx.Γ ctx.criticalPath.firstStep⁆≤
      VAt ctx.Γ ctx.criticalPath.firstStep)
    (hCK : ⁅C,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⊓QAt ctx.Γ middle⁆≤
      ZAt ctx.Γ ctx.criticalPath.a')
    (hindex : (QAt ctx.Γ middle).relIndex (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep))=2)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal]
    [hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep ⧸
      (ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep))] :
    ∀ b:(C⊔VAt ctx.Γ ctx.criticalPath.firstStep:Subgroup G),
      Nat.card ((⁅Subgroup.zpowers (b:G),twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆.subgroupOf
        (VAt ctx.Γ ctx.criticalPath.firstStep)).map (QuotientGroup.mk'
          ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep))))≤4 := by
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.firstStep
  let Z:=ZAt ctx.Γ ctx.criticalPath.firstStep
  let E:=EAt ctx.Γ ctx.criticalPath.firstStep
  let U:=twoCoreIn E
  let Qm:=QAt ctx.Γ middle
  let M:=GAt ctx.Γ middle
  let L:=ZAt ctx.Γ middle
  let BB:=C⊔V
  let K:=U⊓Qm
  let Vbar:=V⧸Z.subgroupOf V
  let π:=QuotientGroup.mk' (Z.subgroupOf V)
  obtain ⟨_,hfirst,_,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hlong : 2<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  let _ : IsElementaryAbelian 2 V:=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hshort).1
  have hBBC : BB≤Subgroup.centralizer (V:Set G):=sup_le hCV
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hcenter:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩
  have hZcard : Nat.card Z=2:=hcenter.1
  have hLV : L≤V:=nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst)
  have hZL : Z≤L:=by
    change Z≤ZAt ctx.Γ middle
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_left
  have hZendL : ZAt ctx.Γ ctx.criticalPath.a'≤L:=by
    change ZAt ctx.Γ ctx.criticalPath.a'≤ZAt ctx.Γ middle
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_right
  have hZV : Z≤V:=hZL.trans hLV
  have hUQ : U≤QAt ctx.Γ ctx.criticalPath.firstStep:=by
    change twoCoreIn (ctx.Γ.twoResidualAt _)≤ctx.Γ.twoCoreAt _
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hVU : ⁅V,U⁆≤Z:=(Subgroup.commutator_mono le_rfl hUQ).trans_eq hcenter.2.1
  have hBU : ⁅BB,U⁆≤V:=(Subgroup.commutator_mono le_rfl (twoCoreIn_le E)).trans hBE
  have hQM : Qm≤M:=by
    change ctx.Γ.twoCoreAt _≤M
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hVM : V≤M:=(show V≤GeneratedNeighborhoodV ctx.Γ middle from le_sSup
    ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,rfl⟩).trans
      ((nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hlong middle).trans hQM)
  have hBK : ⁅BB,K⁆≤L:=by
    have hh:=SectionEight.eight_six_commutator_sSup_le ({C,V}:Set (Subgroup G)) K L M
      (stabilizer_le_normalizer_z ctx.Γ _)
      (by intro D hD;rcases hD with rfl|hD;exact hCQm.trans hQM
          have : D=V:=Set.mem_singleton_iff.mp hD;subst D;exact hVM)
      (by intro D hD;rcases hD with rfl|hD;exact hCK.trans hZendL
          have : D=V:=Set.mem_singleton_iff.mp hD;subst D
          exact ((Subgroup.commutator_mono le_rfl inf_le_left).trans hVU).trans hZL)
    simpa only [sSup_pair] using hh
  have hLcard : Nat.card L=4:=(sectionTenOpeningData ctx middle hpath).center_card
  have hZLindex : Z.relIndex L=2:=by
    have hh:=(Z.subgroupOf L).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv,hZcard,hLcard] at hh
    change Z.relIndex L*2=4 at hh
    omega
  let Lbar:=(L.subgroupOf V).map π
  have hLbarCard : Nat.card Lbar=2:=by
    have hh:=Subgroup.relIndex_ker (L.subgroupOf V) π
    rw [QuotientGroup.ker_mk'] at hh
    have hmap:=Subgroup.relIndex_map_map_of_injective (Z.subgroupOf V) (L.subgroupOf V) V.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hZV,Subgroup.map_subgroupOf_eq_of_le hLV,hZLindex] at hmap
    exact hh.symm.trans hmap.symm
  have hKindex : (K.subgroupOf U).index=2:=by
    change K.relIndex U=2
    rw [Subgroup.inf_relIndex_left]
    exact hindex
  let pairing:=Subgroup.centralQuotientCommutatorPairing BB U V Z le_sup_right hBBC hBU hVU
  intro b
  let f:U→*Vbar:=pairing b
  have hKimage : (K.subgroupOf U).map f≤Lbar:=by
    rintro w ⟨k,hk,rfl⟩
    refine ⟨⟨⁅(b:G),(k:G)⁆,hBU (Subgroup.commutator_mem_commutator b.property k.property)⟩,?_,?_⟩
    · exact hBK (Subgroup.commutator_mem_commutator b.property hk)
    · exact (Subgroup.centralQuotientCommutatorPairing_apply BB U V Z le_sup_right hBBC hBU hVU b k).symm
  have hKcard : Nat.card ((K.subgroupOf U).map f)≤2:=
    (Subgroup.card_le_of_le hKimage).trans_eq hLbarCard
  let R:=(K.subgroupOf U).map f.rangeRestrict
  have hRindex : R.index≤2:=by
    have hh:=(K.subgroupOf U).index_map_dvd f.rangeRestrict_surjective
    rw [hKindex] at hh
    exact Nat.le_of_dvd (by decide) hh
  have hRmap : R.map f.range.subtype=(K.subgroupOf U).map f:=by
    rw [Subgroup.map_map]
    rfl
  have hRcard : Nat.card R≤2:=by
    rw [←Subgroup.card_map_of_injective f.range.subtype_injective,hRmap]
    exact hKcard
  have hcount:=R.index_mul_card
  have hbound : Nat.card f.range≤4:=by nlinarith
  rw [←Subgroup.centralQuotientCommutatorPairing_range BB U V Z le_sup_right hBBC hBU hVU b]
  exact hbound


private theorem residual_core_centralizer_commutators
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hfive : Nonempty (((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep))) ≃* C5)) :
    let C:=QAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') : Set G)
    ⁅C,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆≤ZAt ctx.Γ ctx.criticalPath.firstStep ∧
    ⁅C,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⊓QAt ctx.Γ middle⁆=⊥ := by
  dsimp only
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.firstStep
  let Z:=ZAt ctx.Γ ctx.criticalPath.firstStep
  let E:=EAt ctx.Γ ctx.criticalPath.firstStep
  let U:=twoCoreIn E
  let C:=QAt ctx.Γ ctx.criticalPath.a' ⊓
    Subgroup.centralizer (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'):Set G)
  let BB:=C⊔V
  obtain ⟨hCQm,hPC,hCfirst,_hCinfA,_hCinfV,hCE,hCK⟩:=residual_core_centralizer_setup
    ctx middle hpath hno hfive
  have hQP : QAt ctx.Γ ctx.criticalPath.firstStep≤P:=by
    change ctx.Γ.twoCoreAt _≤P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hCP : C≤P:=(hCfirst.trans inf_le_left).trans hQP
  obtain ⟨hPB,hBE⟩:=first_normalizes_centralizer_enlargement ctx middle hpath C hCP hPC hCE
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hcenter:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩
  obtain ⟨hN,hW,action,hformula,hkernel⟩:=nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩
  let _:=hN
  let _:=hW
  let _ : IsElementaryAbelian 2 V:=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hshort).1
  have hBBC : BB≤Subgroup.centralizer (V:Set G):=sup_le (hCfirst.trans inf_le_right)
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hE : E=twoResidualIn P:=ctx.Γ.twoResidualAt_def _
  have hEP : E≤P:=hE ▸ twoResidualIn_le P
  have hEN : (E.subgroupOf P).Normal:=hE ▸ twoResidualIn_normal P
  let _:=hEN
  have hPU : P≤Subgroup.normalizer (U:Set G):=
    (Subgroup.normal_subgroupOf_iff_le_normalizer ((twoCoreIn_le E).trans hEP)).mp
      (twoCoreIn_normal_of_normal E P hEP hEN)
  have hPV : P≤Subgroup.normalizer (V:Set G):=stabilizer_le_normalizer_v ctx.Γ _
  have hPZ : P≤Subgroup.normalizer (Z:Set G):=stabilizer_le_normalizer_z ctx.Γ _
  have hptwo : IsPGroup 2 (P⧸E.subgroupOf P):=by
    have hn : E.subgroupOf P=twoResidualSubgroup P:=by
      rw [hE,twoResidualIn,twoResidualAmbient]
      exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    have hr : E.subgroupOf P=BenderSuzuki.External.hktPResidual 2 P:=
      hn.trans (SectionThree.twoResidualSubgroup_eq_hktPResidual' P)
    let _ : (BenderSuzuki.External.hktPResidual 2 P).Normal:=
      BenderSuzuki.External.hktPResidual_normal
    exact (BenderSuzuki.External.hktPResidual_quotient_isPGroup (Q:=P) (q:=2)).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hr).symm
  have hZV : Z≤V:=hcenter.2.1.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPV))
  have hUQ : U≤QAt ctx.Γ ctx.criticalPath.firstStep:=by
    change twoCoreIn (ctx.Γ.twoResidualAt _)≤ctx.Γ.twoCoreAt _
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hVU : ⁅V,U⁆≤Z:=(Subgroup.commutator_mono le_rfl hUQ).trans_eq hcenter.2.1
  have hBU : ⁅BB,U⁆≤V:=(Subgroup.commutator_mono le_rfl (twoCoreIn_le E)).trans hBE
  have hVcard : Nat.card V=32:=by
    obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
    obtain ⟨mover,hmove⟩:=(lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    change Nat.card (v ctx.Γ ctx.criticalPath.firstStep)=32
    rw [←hmove,v_act]
    exact (Nat.card_congr ((VAt ctx.Γ ctx.criticalPath.a').equivMapOfInjective
      (MulAut.conj (mover:G)⁻¹).toMonoidHom (MulAut.conj (mover:G)⁻¹).injective).toEquiv).symm.trans
        (ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hZcard : Nat.card Z=2:=hcenter.1
  have hquotCard : Nat.card (V⧸Z.subgroupOf V)=16:=by
    have hh:=Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hZcard,hVcard] at hh
    omega
  have hcomm : ⁅BB,U⁆≤Z:=Subgroup.commutator_le_of_small_irreducible_centralizing_family
    P BB U V Z E hZV le_sup_right hBBC hPB hPU hPV hPZ hEP hptwo hBU hVU hBE action hformula
    (ten_one_large_first_irreducible ctx middle hpath hno action hformula hkernel)
    (fun b=>(first_small_images ctx middle hpath C hCQm (hCfirst.trans inf_le_right)
      hBE hCK (first_core_edge ctx middle hpath).2 b).trans_lt (by rw [hquotCard];decide))
  have hCU : ⁅C,U⁆≤Z:=(Subgroup.commutator_mono le_sup_left le_rfl).trans hcomm
  refine ⟨hCU,?_⟩
  apply bot_unique
  have hh:=le_inf ((Subgroup.commutator_mono le_rfl inf_le_left).trans hCU) hCK
  exact hh.trans_eq (sectionTenOpeningData ctx middle hpath).center_direct_product.2.1.eq_bot

public theorem ten_one_large_residual_core_centralizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hfive : Nonempty (((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep))) ≃* C5)) :
    QAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') : Set G) =
        ZAt ctx.Γ ctx.criticalPath.a' := by
  let C:=QAt ctx.Γ ctx.criticalPath.a' ⊓
    Subgroup.centralizer (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'):Set G)
  obtain ⟨hCQm,hPC,hCfirst,hCinfA,hCinfV,_,_⟩:=
    residual_core_centralizer_setup ctx middle hpath hno hfive
  obtain ⟨hCUfirst,hcoatom⟩:=residual_core_centralizer_commutators ctx middle hpath hno hfive
  apply le_antisymm
  · exact ten_one_large_residual_centralizer_final_transfer ctx middle hpath hno C
      hCQm hPC inf_le_right hCfirst hCinfA hCUfirst hcoatom
  · exact hCinfV.symm.le.trans inf_le_left

end Stellmacher.SectionTen
