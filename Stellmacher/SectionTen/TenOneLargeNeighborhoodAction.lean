module
public import Stellmacher.SectionTen.TenOneLargeOmegaCenter
public import Stellmacher.SectionTen.TenOneLargeGeneratedTerminalIntersection
public import Theory.GroupTheory.Commutator.BoundedImageKernel

/-!
# The generated subgroup index and terminal-edge action in the large branch

In the no-transvection Section Ten configuration, W has index four over
the common first/terminal module intersection I, and its commutator with
the middle/terminal edge stabilizer lies in the terminal module V.

The valid omega-center equality and residual fixed-component splitting give
C_W(V)≤V. The actual transported seed identifies W∩V as order sixteen,
and it is index two in V. Since [W,V] lies in the terminal center of order
two, the bounded-image kernel theorem gives |W|≤32. The proved W≰V gives
the reverse bound, hence |W/I|=4. Triple-commutator rotation puts [U,U] in
C(V), where U=O₂(E_terminal); W is U-normal, so [W,U]≤C_W(V)≤V.
The cubic edge equality edge=Q_middle∨U combines this with [W,Q_middle]≤I.

Source: Stellmacher (10.1)(17), printed p.64 of
`refs/files/stellmacher-n-group.pdf`. This proof uses the correct order-sixteen
centralizer intersection rather than the inconsistent printed C_W(V)=I.
No source-(18) quotient order or Frobenius model is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem generated_index_of_omega
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hOmega : omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)=
      VAt ctx.Γ ctx.criticalPath.firstStep⊓VAt ctx.Γ ctx.criticalPath.a') :
    QuotientCardEq (conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle))
      (VAt ctx.Γ ctx.criticalPath.firstStep⊓VAt ctx.Γ ctx.criticalPath.a') 4 := by
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let I:=VAt ctx.Γ ctx.criticalPath.firstStep⊓V
  let O:=omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)
  let W:=conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ middle)
  let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔O
  let D:=(Y⊔V)⊓Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a':Set G)
  let M:=W⊓V
  let _ : IsElementaryAbelian 2 W:=ten_one_generated_elementary ctx middle hpath
  obtain ⟨hsplit,hDO,_hOeq,_hPD,_hDV⟩:=ten_one_large_omega_fixed_component ctx middle hpath hno
  have hDV : D≤V:=hDO.trans (hOmega.le.trans inf_le_right)
  have hYV : Y≤V:=by
    apply le_trans le_sup_left
    change Y⊔V≤V
    exact hsplit.le.trans (sup_le le_rfl hDV)
  have hCW : W⊓Subgroup.centralizer (V:Set G)≤V:=le_sup_left.trans hYV
  obtain ⟨hMcard,hWnot⟩:=ten_one_large_generated_terminal_intersection ctx middle hpath hno
  obtain ⟨_,_,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hZcard,hVQ,_⟩:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  have hWQ : W≤QAt ctx.Γ ctx.criticalPath.a':=(ten_one_generated_containment ctx middle hpath).trans
    (inf_le_left.trans (sInf_le ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩))
  have hcomm : ⁅W,V⁆≤Z:=by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hWQ).trans_eq hVQ
  have hZW : Z≤W:=by
    obtain ⟨_,hfirst,_,_⟩:=sectionTenOpeningGeometry ctx middle hpath
    have hZI : Z≤I:=by
      have hmid:ZAt ctx.Γ middle≤I:=le_inf
        (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst))
        (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))
      apply le_trans ?_ hmid
      rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
      exact le_sup_right
    exact hZI.trans (ten_one_common_intersection_le_generated ctx middle)
  have hVcard : Nat.card V=32:=(ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hMindex : M.relIndex V=2:=by
    have hh:=(M.subgroupOf V).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show M≤V from inf_le_right)).toEquiv,
      hMcard,hVcard] at hh
    change M.relIndex V*16=32 at hh
    omega
  have hMCW : M≤Subgroup.centralizer (W:Set G):=inf_le_left.trans
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  obtain ⟨K,hKW,hcount,hKV⟩:=Subgroup.exists_large_subgroup_commutator_le_of_index_two
    W W V M ⊥ Z le_rfl inferInstance hZW hcomm inf_le_right hMCW hMindex
  rw [Subgroup.relIndex_bot_left,hZcard] at hcount
  have hKM : K≤M:=le_inf hKW ((le_inf hKW
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hKV))).trans hCW)
  have hWbound : Nat.card W≤32:=by
    have hh:=Subgroup.card_le_of_le hKM
    rw [hMcard] at hh
    omega
  have hindexNe : M.relIndex W≠1:=by
    intro h
    exact hWnot ((Subgroup.relIndex_eq_one.mp h).trans inf_le_right)
  have hcountW:=(M.subgroupOf W).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show M≤W from inf_le_left)).toEquiv,hMcard] at hcountW
  have hindexPos : 0<M.relIndex W:=Nat.pos_of_ne_zero (M.subgroupOf W).index_ne_zero_of_finite
  have hWcard : Nat.card W=32:=by
    change M.relIndex W*16=Nat.card W at hcountW
    omega
  change Nat.card W=4*Nat.card I
  rw [hWcard,(ten_one_large_terminal_structure ctx middle hpath hno).2.2]


private theorem generated_edge_commutator_of_omega
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hOmega : omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)=
      VAt ctx.Γ ctx.criticalPath.firstStep⊓VAt ctx.Γ ctx.criticalPath.a') :
    ⁅conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle),
      GAt ctx.Γ middle⊓GAt ctx.Γ ctx.criticalPath.a'⁆≤VAt ctx.Γ ctx.criticalPath.a' := by
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let Pm:=GAt ctx.Γ middle
  let Q:=QAt ctx.Γ middle
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let O:=omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)
  let W:=conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a') Pm
  let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔O
  let D:=(Y⊔V)⊓Subgroup.centralizer (E:Set G)
  let edge:=Pm⊓P
  obtain ⟨hsplit,hDO,_hOeq,_hPD,_hDV⟩:=ten_one_large_omega_fixed_component ctx middle hpath hno
  have hDV : D≤V:=hDO.trans (hOmega.le.trans inf_le_right)
  have hYV : Y≤V:=by
    apply le_trans le_sup_left
    change Y⊔V≤V
    exact hsplit.le.trans (sup_le le_rfl hDV)
  have hCW : W⊓Subgroup.centralizer (V:Set G)≤V:=le_sup_left.trans hYV
  have hWU : W≤U:=(ten_one_large_first_residual_index ctx middle hpath hno).2
  obtain ⟨_,_,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hUQ : U≤QAt ctx.Γ ctx.criticalPath.a':=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hEP : E≤P:=by
    change ctx.Γ.twoResidualAt ctx.criticalPath.a'≤P
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hUP : U≤P:=(twoCoreIn_le E).trans hEP
  have hUm : U≤Pm:=hUQ.trans (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2)
  have hVU : ⁅V,U⁆≤Z:=(Subgroup.commutator_mono le_rfl hUQ).trans_eq
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort
      ctx.criticalPath.a' ⟨alignment,halign⟩).2.1
  have hZcentral : Z≤Subgroup.centralizer (U:Set G):=Subgroup.le_centralizer_iff.mp
    (hUP.trans (nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.a' ⟨alignment,halign⟩))
  have hZU : ⁅Z,U⁆=⊥:=Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZcentral
  have hVUzero : ⁅⁅V,U⁆,U⁆=⊥:=bot_unique
    ((Subgroup.commutator_mono hVU le_rfl).trans_eq hZU)
  have hUVzero : ⁅⁅U,V⁆,U⁆=⊥:=by rw [Subgroup.commutator_comm U V];exact hVUzero
  have hUU : ⁅⁅U,U⁆,V⁆=⊥:=Subgroup.commutator_commutator_eq_bot_of_rotate hUVzero hVUzero
  have hWnorm : Pm≤Subgroup.normalizer (W:Set G):=by
    dsimp only [W]
    rw [conjugateClosure,Subgroup.le_normalizer_closure_iff]
    intro mover hmover point hpoint
    obtain ⟨earlier,element,rfl⟩:=hpoint
    apply Subgroup.subset_closure
    refine ⟨⟨mover*(earlier:G),Pm.mul_mem hmover earlier.property⟩,element,?_⟩
    change mover*((earlier:G)*(element:G)*(earlier:G)⁻¹)*mover⁻¹=
      (mover*(earlier:G))*(element:G)*(mover*(earlier:G))⁻¹
    group
  have hWUC : ⁅W,U⁆≤Subgroup.centralizer (V:Set G):=
    (Subgroup.commutator_mono hWU le_rfl).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUU)
  have hWUV : ⁅W,U⁆≤V:=(le_inf
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hUm.trans hWnorm)) hWUC).trans hCW
  have hQm : Q≤Pm:=by
    change ctx.Γ.twoCoreAt middle≤Pm
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQP : Q≤P:=((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal) default).2.2
  have hQedge : Q≤edge:=le_inf hQm hQP
  have hUedge : U≤edge:=le_inf hUm hUP
  have hescape : ¬U≤Q:=nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.a' middle ⟨alignment,halign⟩
      (ctx.Γ.adjacent_symm hterminal)
  have hcard : Nat.card edge=2*Nat.card Q:=
    (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
      (sectionTenOpeningData ctx middle hpath).quotient_model).edge_card _ hterminal
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
  have hQWV : ⁅Q,W⁆≤V:=by
    rw [Subgroup.commutator_comm]
    exact (ten_one_large_generated_core_commutator ctx middle hpath hno).trans inf_le_right
  have hUWV : ⁅U,W⁆≤V:=by rw [Subgroup.commutator_comm];exact hWUV
  have hh:=SectionEight.eight_six_commutator_sSup_le ({Q,U}:Set (Subgroup G)) W V P
    (stabilizer_le_normalizer_v ctx.Γ _)
    (by intro K hK;rcases hK with rfl|hK;exact hQP
        have : K=U:=Set.mem_singleton_iff.mp hK;subst K;exact hUP)
    (by intro K hK;rcases hK with rfl|hK;exact hQWV
        have : K=U:=Set.mem_singleton_iff.mp hK;subst K;exact hUWV)
  change ⁅W,edge⁆≤V
  rw [hgen,Subgroup.commutator_comm]
  simpa only [sSup_pair] using hh

public theorem ten_one_large_neighborhood_action
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    : QuotientCardEq
      (conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle))
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a') 4 ∧
      ⁅conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle), GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a'⁆ ≤
        VAt ctx.Γ ctx.criticalPath.a' := by
  have hOmega := ten_one_large_neighborhood_omega_center ctx middle hpath hno
  exact ⟨generated_index_of_omega ctx middle hpath hno hOmega,
    generated_edge_commutator_of_omega ctx middle hpath hno hOmega⟩
end Stellmacher.SectionTen
