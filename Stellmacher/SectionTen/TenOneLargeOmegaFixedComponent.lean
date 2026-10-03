module
public import Stellmacher.SectionTen.TenOneLargeCentralizerCoreAction
public import Stellmacher.SectionTen.TenOneLargeTerminalResidualCentralizer
public import Stellmacher.SectionTen.TenOneNeighborhoodSmallDisplacement
public import Theory.GroupTheory.ResidualCentralLayerSplitting

/-!
# The residual fixed component inside the neighborhood omega center

In the actual no-transvection Section Ten context, let Y be C_W(Vend)
joined with the neighborhood omega center and let D=C_(YVend)(Eend).
Then YVend=Vend D, D lies in the neighborhood omega center O, and O=I D
for the common endpoint-module intersection I. The packet also records
Gend-normalization of D and D∩Vend=Zend.

Residual central-layer splitting gives the first factorization. Full odd
support identifies the fixed intersection with Vend. Mutual centralizers
bound [D,Vfirst] by Zend; the actual neighborhood small-displacement theorem
makes D centralize Vfirst. Since D centralizes Eend, the terminal residual
core's punctured cubic transitivity carries this to every neighborhood
module, proving D≤O. Factoring elements of O inside the elementary group
YVend and using O∩Vend=I gives O=I D.

This is the valid fixed-component step on printed p.64 of Stellmacher
(10.1)(16), Journal of Algebra 190 (1997). The printed first equality
C_W(Vend)=I conflicts with the order-sixteen seed in W∩Vend and is not used.
The argument also does not assert Y=O. The final local centralizer-transitivity
step that forces D=Zend is separate.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_omega_fixed_component
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let V:=VAt ctx.Γ ctx.criticalPath.a'
    let Wnext:=GeneratedNeighborhoodV ctx.Γ middle
    let W:=conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)
    let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔omegaOneCenter Wnext
    let D:=(Y⊔V)⊓Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a':Set G)
    Y⊔V=V⊔D ∧ D≤omegaOneCenter Wnext ∧
      omegaOneCenter Wnext=(VAt ctx.Γ ctx.criticalPath.firstStep⊓V)⊔D ∧
      GAt ctx.Γ ctx.criticalPath.a'≤Subgroup.normalizer (D:Set G) ∧
      D⊓V=ZAt ctx.Γ ctx.criticalPath.a' := by
  dsimp only
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let Pm:=GAt ctx.Γ middle
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let Wnext:=GeneratedNeighborhoodV ctx.Γ middle
  let W:=conjugateClosure (A⊓QAt ctx.Γ ctx.criticalPath.a') Pm
  let O:=omegaOneCenter Wnext
  let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔O
  let BB:=Y⊔V
  let I:=A⊓V
  let D:=BB⊓Subgroup.centralizer (E:Set G)
  obtain ⟨hBB,hYW,_hYC,hPB,hBE,_hYK,hIO,hOVI⟩:=ten_one_large_centralizer_setup ctx middle hpath hno
  let _ : IsElementaryAbelian 2 BB:=hBB
  obtain ⟨_,hfirst,hterminal,hends⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hlong : 2<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hE : E=twoResidualIn P:=by
    change ctx.Γ.twoResidualAt ctx.criticalPath.a'=twoResidualIn P
    rw [ctx.Γ.twoResidualAt_def]
    rfl
  have hEP : E≤P:=hE ▸ twoResidualIn_le P
  have hEN : (E.subgroupOf P).Normal:=hE ▸ twoResidualIn_normal P
  have hPE : P≤Subgroup.normalizer (E:Set G):=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp hEN
  have hPD : P≤Subgroup.normalizer (D:Set G):=
    (le_inf hPB (hPE.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hUtwo : IsPGroup 2 U:=(pCore_isPGroup (p:=2) (G:=E)).map E.subtype
  have hUN : (U.subgroupOf E).Normal:=twoCoreIn_normal E
  let _:=hUN
  have hUeq : U.subgroupOf E=pCore 2 E:=Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
  have hodd : Odd (Nat.card (E⧸U.subgroupOf E)):=by
    have hh : Odd (Nat.card (E⧸pCore 2 E)):=by
      rw [hE]
      exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ ctx.criticalPath.a' middle
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) P le_rfl
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hUeq).toEquiv]
    exact hh
  have hperfect : ∀ N:Subgroup E, ∀ hN:N.Normal, let _:=hN; IsPGroup 2 (E⧸N)→N=⊤:=by
    intro N hN
    dsimp only
    intro htwo
    have hh:=BenderSuzuki.External.hktPResidual_le N hN htwo
    have heq : BenderSuzuki.External.hktPResidual 2 E=⊤:=by
      rw [hE]
      exact twoResidualAmbient_has_top_twoResidual P
    exact top_unique (heq ▸ hh)
  have hVCE : V⊓Subgroup.centralizer (E:Set G)=Z:=
    ten_one_large_terminal_residual_centralizer ctx middle hpath hno
  have hZV : Z≤V:=hVCE.symm.le.trans inf_le_left
  have hZCE : Z≤Subgroup.centralizer (E:Set G):=hVCE.symm.le.trans inf_le_right
  have hBU : ⁅BB,U⁆≤Z:=ten_one_large_centralizer_core_commutator ctx middle hpath hno
  have hsplit : BB=V⊔D:=Subgroup.eq_sup_centralizer_of_no_two_quotient_central_layer
    E U BB V Z (twoCoreIn_le E) hUtwo (IsElementaryAbelian.isPGroup 2 BB) hodd hperfect
    (hEP.trans hPB) le_sup_right (hZV.trans le_sup_right) hZCE hBE hBU
  have hVW : V≤Wnext:=le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩
  have hBBW : BB≤Wnext:=sup_le hYW hVW
  have hDW : D≤Wnext:=inf_le_left.trans hBBW
  have hWQ : Wnext≤QAt ctx.Γ middle:=nine_seven_neighborhood_le_own_core
    ctx.toLocalContext.toSectionNineLocalContext hlong middle
  have hDA : D≤Subgroup.normalizer (A:Set G):=
    (hDW.trans hWQ).trans ((((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2).trans
        (stabilizer_le_normalizer_v ctx.Γ _))
  have hAP : A≤P:=(lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
  have hcommD : ⁅D,A⁆≤D:=Subgroup.le_normalizer_iff_commutator_le_left.mp (hAP.trans hPD)
  have hDCV : D≤Subgroup.centralizer (V:Set G):=inf_le_left.trans
    ((Subgroup.le_centralizer_iff_isMulCommutative.mpr (inferInstance:IsMulCommutative BB)).trans
      (Subgroup.centralizer_le (show V≤BB from le_sup_right)))
  have hcommI : ⁅D,A⁆≤I:=by
    have hh:=le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp hDA) (hcommD.trans hDCV)
    exact hh.trans_eq (ten_one_large_mutual_centralizers ctx middle hpath hno).1
  have hcommZ : ⁅D,A⁆≤Z:=(le_inf (hcommI.trans inf_le_right)
    (hcommD.trans inf_le_right)).trans_eq hVCE
  have hDCA : D≤Subgroup.centralizer (A:Set G):=by
    intro d hd
    apply ten_one_neighborhood_actor_centralizes_first_of_small_commutator ctx middle hpath hno d (hDW hd)
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hd) le_rfl).trans hcommZ
  have hUC : U≤Subgroup.centralizer (D:Set G):=(twoCoreIn_le E).trans
    (Subgroup.le_centralizer_iff.mp (show D≤Subgroup.centralizer (E:Set G) from inf_le_right))
  have hUQend : U≤QAt ctx.Γ ctx.criticalPath.a':=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hQP : QAt ctx.Γ ctx.criticalPath.a'≤P:=by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a'≤P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hUedge : U≤Pm⊓P:=le_inf
    (hUQend.trans (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2))
    (hUQend.trans hQP)
  have hescape:=nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.a' middle ⟨alignment,halign⟩
      (ctx.Γ.adjacent_symm hterminal)
  have htrans:=(cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
    (sectionTenOpeningData ctx middle hpath).quotient_model).punctured_transitivity
      ctx.criticalPath.a' hterminal U hUedge hescape
  have hDCW : D≤Subgroup.centralizer (Wnext:Set G):=by
    apply Subgroup.le_centralizer_iff.mp
    apply sSup_le
    rintro K ⟨neighbor,hneighbor,rfl⟩
    by_cases heq : neighbor=ctx.criticalPath.a'
    · subst neighbor
      exact Subgroup.le_centralizer_iff.mp hDCV
    obtain ⟨actor,hmove⟩:=htrans
      ⟨(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,hends⟩ ⟨hneighbor,heq⟩
    change ctx.Γ.act (actor:G) ctx.criticalPath.firstStep=neighbor at hmove
    change v ctx.Γ neighbor≤Subgroup.centralizer (D:Set G)
    rw [←hmove,v_act]
    rintro x ⟨a,ha,rfl⟩
    exact (Subgroup.centralizer (D:Set G)).mul_mem
      ((Subgroup.centralizer (D:Set G)).mul_mem
        ((Subgroup.centralizer (D:Set G)).inv_mem (hUC actor.property))
        ((Subgroup.le_centralizer_iff.mp hDCA) ha))
      (by simpa using hUC actor.property)
  have hDO : D≤O:=by
    intro d hd
    exact (mem_omegaOneCenterAmbient_iff Wnext d).mpr
      ⟨hDW hd,elemPow_eq_one_of_isElementaryAbelian (p:=2) d hd.1,
        Subgroup.mem_centralizer_iff.mp (hDCW hd)⟩
  have hOB : O≤BB:=le_sup_right.trans le_sup_left
  have hDB : D≤BB:=inf_le_left
  have hVDnormal : (D.subgroupOf BB).Normal:=inferInstance
  let _:=hVDnormal
  have hOeq : O=I⊔D:=by
    apply le_antisymm
    · intro o ho
      have hh : (⟨o,hOB ho⟩:BB)∈V.subgroupOf BB⊔D.subgroupOf BB:=by
        rw [←Subgroup.subgroupOf_sup (show V≤BB from le_sup_right) hDB]
        exact hsplit ▸ hOB ho
      obtain ⟨v,hv,d,hd,heq⟩:=Subgroup.mem_sup_of_normal_right.mp hh
      have heqG : (v:G)*(d:G)=o:=congrArg Subtype.val heq
      have hvO : (v:G)∈O:=by
        have hvEq : (v:G)=o*(d:G)⁻¹:=(eq_mul_inv_iff_mul_eq).mpr heqG
        rw [hvEq]
        exact O.mul_mem ho (O.inv_mem (hDO hd))
      rw [←heqG]
      exact (I⊔D).mul_mem (Subgroup.mem_sup_left (hOVI ⟨hvO,hv⟩)) (Subgroup.mem_sup_right hd)
    · exact sup_le hIO hDO
  have hDV : D⊓V=Z:=by
    calc
      D⊓V=V⊓Subgroup.centralizer (E:Set G):=by
        ext x
        constructor
        · exact fun hx=>⟨hx.2,hx.1.2⟩
        · exact fun hx=>⟨⟨(show V≤BB from le_sup_right) hx.1,hx.2⟩,hx.1⟩
      _=Z:=hVCE
  exact ⟨hsplit,hDO,hOeq,hPD,hDV⟩

end Stellmacher.SectionTen
