module
public import Stellmacher.SectionTen.TenOneLargeTerminalFullSupport
public import Theory.GroupAction.NativeCoprimeQuotientFixedCard
public import Stellmacher.ResidualCoreCommutator

/-!
# The full quotient action of the actual odd complement on U/V

Keep the original large Section Ten context, an actual three-group D
supplementing U=O₂(E) in E, and the chosen source-(18) normality and
elementary structure of U/V with [U,Q] ≤ V. This constructs a literal
P-conjugation action on that same quotient, retaining its normalizer
witness and formula. Its exact restriction to D has trivial whole fixed
subgroup. The construction also supplies the actual containment V ≤ U.

Full residual action on V gives V ≤ U. Residual perfection and the actual
odd E/O₂(E) quotient give U=[U,E]. The quotient action factory therefore
has full E-image support. Its core kernel kills U, so E=U∨D identifies
the D-image with the E-image. This is a three-group acting coprimely on
the elementary two-quotient. Fixed-point/commutator splitting makes its
fixed subgroup trivial, and the literal restriction along D ≤ P has the
same fixed points. No faithfulness or irreducibility of U/V is assumed.

Source: Stellmacher (10.1), printed p.64, the quotient fixed-factor step
between (18) and (19). Cardinality16 and the chosen actor lines are used
only in the following fixed-factor theorem.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_nine_core_action
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (D:Subgroup G) (_hDE:D≤EAt ctx.Γ ctx.criticalPath.a')
    (hDP:D≤GAt ctx.Γ ctx.criticalPath.a')
    (hgen:EAt ctx.Γ ctx.criticalPath.a'=twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⊔D)
    (hD:IsPGroup 3 D)
    (hN:((VAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))).Normal) :
    let _:=hN
    let P:=GAt ctx.Γ ctx.criticalPath.a'
    let E:=EAt ctx.Γ ctx.criticalPath.a'
    let U:=twoCoreIn E
    let V:=VAt ctx.Γ ctx.criticalPath.a'
    let X:=U⧸V.subgroupOf U
    IsElementaryAbelian 2 X → ⁅U,QAt ctx.Γ ctx.criticalPath.a'⁆≤V →
    V≤U ∧ ∃ hPU:P≤Subgroup.normalizer (U:Set G), ∃ action:P→*MulAut X,
      (∀ p:P,∀ u:U,action p (QuotientGroup.mk' (V.subgroupOf U) u)=
        QuotientGroup.mk' (V.subgroupOf U)
          ⟨(p:G)*(u:G)*(p:G)⁻¹,(Subgroup.mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) ∧
      (let _ : MulDistribMulAction D X:=MulDistribMulAction.compHom X
        (action.comp (Subgroup.inclusion hDP))
       FixedPoints.subgroup (⊤:Subgroup D) X=⊥) := by
  let _:=hN
  dsimp only
  intro hel hUQcomm
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Q:=QAt ctx.Γ ctx.criticalPath.a'
  let X:=U⧸V.subgroupOf U
  let _ : IsElementaryAbelian 2 X:=hel
  have hE:E=twoResidualIn P:=ctx.Γ.twoResidualAt_def _
  have hEP:E≤P:=hE ▸ twoResidualIn_le P
  have hUP:U≤P:=(twoCoreIn_le E).trans hEP
  have hPU:P≤Subgroup.normalizer (U:Set G):=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV:P≤Subgroup.normalizer (V:Set G):=stabilizer_le_normalizer_v ctx.Γ _
  have hshort:1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hVQ:V≤Q:=neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort _
  have hVfull:⁅V,E⁆=V:=ten_one_large_terminal_residual_full ctx middle hpath hno
  have hVU:V≤U:=by
    rw [←hVfull,Subgroup.commutator_comm]
    apply le_trans (Subgroup.commutator_mono le_rfl hVQ)
    change ⁅E,ctx.Γ.twoCoreAt ctx.criticalPath.a'⁆≤twoCoreIn E
    rw [hE,ctx.Γ.twoCoreAt_def]
    exact residual_commutator_core_le P
  obtain ⟨_,_,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hperfect:BenderSuzuki.External.hktPResidual 2 E=⊤:=by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  have hodd:Odd (Nat.card (E⧸pCore 2 E)):=by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ ctx.criticalPath.a' middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) P le_rfl
  have hfullU:⁅U,E⁆=U:=by
    have hh:=congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh.symm
  obtain ⟨action,hformula,hQker,hfull⟩:=Subgroup.exists_quotient_conjugation_full_action
    P U V E Q hPU hPV hN hEP hfullU hUQcomm
  let F:=(E.subgroupOf P).map action
  have hUQ:U≤Q:=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hUk:U.subgroupOf P≤action.ker:=
    (show U.subgroupOf P≤Q.subgroupOf P from fun _ hu=>hUQ hu).trans hQker
  have hDimage:(D.subgroupOf P).map action=F:=by
    have hg:E=U⊔D:=hgen
    dsimp only [F]
    rw [hg,Subgroup.subgroupOf_sup hUP hDP,Subgroup.map_sup]
    have hk:(U.subgroupOf P).map action=⊥:=by
      rw [Subgroup.map_eq_bot_iff]
      exact hUk
    rw [hk,bot_sup_eq]
  have hDnative:IsPGroup 3 (D.subgroupOf P):=hD.of_equiv (Subgroup.subgroupOfEquivOfLe hDP).symm
  have hF:IsPGroup 3 F:=hDimage ▸ hDnative.map action
  have hcop:Nat.Coprime (Nat.card F) (Nat.card X):=by
    obtain ⟨a,ha⟩:=hF.exists_card_eq
    obtain ⟨b,hb⟩:=(IsElementaryAbelian.isPGroup 2 X).exists_card_eq
    rw [ha,hb]
    exact ((show Nat.Coprime 3 2 by decide).pow_left a).pow_right b
  have hFfix:FixedPoints.subgroup F X=⊥:=by
    have hh:=(isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G:=X) (A:=F) (Group.isSolvable_of_comm fun a b=>mul_comm a b) hcop inferInstance).disjoint
    change Disjoint (FixedPoints.subgroup F X) (commutatorAction F X) at hh
    rw [hfull,disjoint_top] at hh
    exact hh
  refine ⟨hVU,hPU,action,hformula,?_⟩
  let _ : MulDistribMulAction D X:=MulDistribMulAction.compHom X
    (action.comp (Subgroup.inclusion hDP))
  apply bot_unique
  intro x hx
  apply hFfix.le
  intro f
  obtain ⟨p,hp,hpf⟩:=(show (f:MulAut X)∈(D.subgroupOf P).map action from hDimage.symm ▸ f.property)
  have hh:=hx ⟨⟨p,hp⟩,Subgroup.mem_top _⟩
  change (f:MulAut X) x=x
  rw [←hpf]
  exact hh
end Stellmacher.SectionTen
