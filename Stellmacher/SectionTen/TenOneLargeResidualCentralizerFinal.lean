module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionNine.CubicEdgeGeneration
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Stellmacher.SectionNine.NineFivePenultimateCoreEscapeReduction
public import Stellmacher.SectionNine.NineFivePenultimateJoinAction
public import Stellmacher.OmegaOneCenterMap

/-!
# Final transfer for the large residual-core centralizer

This proves the last containment before (10.1)(20) from the actual seven-part
centralizer packet. The original ambient Section Ten context, middle vertex,
no-transvection hypothesis, and subgroup `C` are retained. In particular, the
normality of `C Z_middle` and its centralization of the middle core are proved
from the packet rather than assumed.

The terminal edge normalizes `C Z_middle`; the first residual core also
normalizes it because its commutator with `C` lies in `Z_first`. That residual
core escapes the middle core, so the cubic local action supplies the remaining
generator of the middle stabilizer. Both the middle-core commutator of
`C Z_middle` and its square-generated subgroup are then middle-normal and lie
in `C`. The endpoint transport of (7.6) shows that any such subgroup centralizing
the terminal residual core centralizes the whole middle residual. The exact
(7.5)(c) centralizer conclusion kills both subgroups. Thus `C Z_middle` lies in
`Ω₁ Z(Q_middle) = Z_middle`, and the supplied first-module intersection puts
`C` in `Z_terminal`.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.65, immediately
before (10.1)(20). The normal-closure step establishes centralization of the
whole residual before applying (7.5)(c).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped Pointwise commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G→*H} {T A B : Subgroup G}

private theorem middle_normal_centralizer_core_eq_bot
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (N : Subgroup G) (hNQ : N≤QAt ctx.Γ middle)
    (hMN : GAt ctx.Γ middle≤normalizer (N:Set G))
    (hNU : N≤centralizer (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'):Set G)) : N=⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let M := GAt Γ middle
  let E := EAt Γ middle
  let U := twoCoreIn (EAt Γ cp.a')
  let K := centralizer (N:Set G)
  have hMK : M≤normalizer (K:Set G) := hMN.trans
    ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (N:Set G))).mp inferInstance)
  have hUK : U≤K := le_centralizer_iff.mp hNU
  obtain ⟨actor,hleft,hright⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpen : cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩=middle := by
    obtain ⟨i,hi,hmid⟩ := hpath
    have hindex : (⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩:Fin (cp.length+1))=i := by
      apply Fin.ext
      have hlen : cp.length=3 := ctx.critical_length
      change cp.length-1=i.val
      omega
    rw [hindex]
    exact hmid
  have hmiddle : Γ.act actor cp.a=middle := hleft.trans hpen
  let f := MulAut.conj actor⁻¹
  have hMmap : (GAt Γ cp.a).map f.toMonoidHom=M :=
    (stabilizer_act Γ actor cp.a).symm.trans (congrArg (GAt Γ) hmiddle)
  have hPmap : (GAt Γ cp.firstStep).map f.toMonoidHom=GAt Γ cp.a' :=
    (stabilizer_act Γ actor cp.firstStep).symm.trans (congrArg (GAt Γ) hright)
  have hEmap : (EAt Γ cp.a).map f.toMonoidHom=E := by
    change (Γ.twoResidualAt cp.a).map f.toMonoidHom=Γ.twoResidualAt middle
    rw [Γ.twoResidualAt_def,Γ.twoResidualAt_def]
    exact map_twoResidualAmbient_of_subgroup_image _ f.toMonoidHom M hMmap
  have hEfmap : (EAt Γ cp.firstStep).map f.toMonoidHom=EAt Γ cp.a' := by
    change (Γ.twoResidualAt cp.firstStep).map f.toMonoidHom=Γ.twoResidualAt cp.a'
    rw [Γ.twoResidualAt_def,Γ.twoResidualAt_def]
    exact map_twoResidualAmbient_of_subgroup_image _ f.toMonoidHom _ hPmap
  have hUmap : (twoCoreIn (EAt Γ cp.firstStep)).map f.toMonoidHom=U := by
    change _=twoCoreIn (EAt Γ cp.a')
    rw [←hEfmap,twoCoreIn_map_equiv]
  have hEK : E≤K := by
    rw [←hEmap]
    apply (map_mono (f:=f.toMonoidHom)
      (lemma_seven_six ctx.sectionSeven Γ cp).next_residual_core.2).trans
    apply map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨m,r,rfl⟩
    change f ((m:G)*(r:G)*(m:G)⁻¹)∈K
    rw [map_mul,map_mul,map_inv]
    have hmM : f (m:G)∈M := hMmap ▸ mem_map_of_mem f.toMonoidHom m.property
    have hrU : f (r:G)∈U := hUmap ▸ mem_map_of_mem f.toMonoidHom r.property
    exact (mem_normalizer_iff.mp (hMK hmM) _).mp (hUK hrU)
  have hfaithful := nine_five_initial_orbit_residual_centralizer
    ctx.toLocalContext.toSectionNineLocalContext middle (sectionTenOpeningGeometry ctx middle hpath).1
  apply bot_unique
  rw [←hfaithful]
  exact le_inf hNQ (le_centralizer_iff.mp hEK)

public theorem ten_one_large_residual_centralizer_final_transfer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (_hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (C : Subgroup G)
    (hCQ : C≤QAt ctx.Γ middle)
    (hPC : GAt ctx.Γ ctx.criticalPath.a'≤normalizer (C:Set G))
    (hCU : C≤centralizer (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'):Set G))
    (_hCfirst : C≤QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      centralizer (VAt ctx.Γ ctx.criticalPath.firstStep:Set G))
    (hCA : C⊓VAt ctx.Γ ctx.criticalPath.firstStep=ZAt ctx.Γ ctx.criticalPath.a')
    (hCfirstU : ⁅C,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆≤
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (_hCfirstUQ : ⁅C,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⊓QAt ctx.Γ middle⁆=⊥) :
    C≤ZAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let M := GAt Γ middle
  let Q := QAt Γ middle
  let Z := ZAt Γ middle
  let U := twoCoreIn (EAt Γ cp.firstStep)
  let X := C⊔Z
  obtain ⟨_,hfirst,hterminal,hne⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hopen := sectionTenOpeningData ctx middle hpath
  have hZomega : Z=omegaOneCenter Q := hopen.center_omega
  have hZdata (z:G) (hz:z∈Z) : z∈Q ∧ z^2=1 ∧ ∀q∈Q,q*z=z*q := by
    have hzomega : z∈omegaOneCenter Q := hZomega ▸ hz
    exact (mem_omegaOneCenterAmbient_iff Q z).mp hzomega
  have hZQ : Z≤Q := fun z hz=>(hZdata z hz).1
  have hZcentral : Z≤centralizer (Q:Set G) := by
    intro z hz
    exact mem_centralizer_iff.mpr (hZdata z hz).2.2
  have hMQ : M≤normalizer (Q:Set G) := stabilizer_le_normalizer_q Γ middle
  have hMZ : M≤normalizer (Z:Set G) := stabilizer_le_normalizer_z Γ middle
  have hQself : Q≤M := by
    change Γ.twoCoreAt middle≤Γ.stabilizer middle
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQterminal : Q≤GAt Γ cp.a' := ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
    middle cp.a' ((mem_neighborhood_iff_adjacent Γ).mpr hterminal) default).2.2
  have hQC : Q≤normalizer (C:Set G) := hQterminal.trans hPC
  have hZC : Z≤normalizer (C:Set G) :=
    (hZcentral.trans (centralizer_le hCQ)).trans (Subgroup.centralizer_le_normalizer _)
  have hUfirstQ : U≤QAt Γ cp.firstStep := by
    change twoCoreIn (Γ.twoResidualAt cp.firstStep)≤Γ.twoCoreAt cp.firstStep
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hUfirst : U≤GAt Γ cp.firstStep := hUfirstQ.trans (by
    change Γ.twoCoreAt cp.firstStep≤Γ.stabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _)
  have hUM : U≤M := hUfirstQ.trans ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
    cp.firstStep middle ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirst)) default).2.2
  have hZfirst : ZAt Γ cp.firstStep≤Z := by
    have heq : Z=ZAt Γ cp.firstStep⊔ZAt Γ cp.a' := hopen.center_direct_product.1
    rw [heq]
    exact le_sup_left
  have hUX : U≤normalizer (X:Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact nine_five_commutator_join_le C Z U X
      (le_sup_left.trans X.le_normalizer) (le_sup_right.trans X.le_normalizer)
      (hCfirstU.trans (hZfirst.trans le_sup_right))
      ((le_normalizer_iff_commutator_le_left.mp (hUM.trans hMZ)).trans le_sup_right)
  have hedgeX : M⊓GAt Γ cp.a'≤normalizer (X:Set G) :=
    (le_inf (inf_le_right.trans hPC) (inf_le_left.trans hMZ)).trans
      (C.normalizer_inf_normalizer_le_normalizer_sup Z)
  have hescape : ¬U≤Q := nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext cp.firstStep middle
      ⟨1,Γ.act_one _⟩ (Γ.adjacent_symm hfirst)
  obtain ⟨actor,hactorU,hactorQ⟩ := SetLike.not_le_iff_exists.mp hescape
  have hgen := cubic_edge_sup_zpowers_eq_stabilizer ctx.sectionSeven Γ middle cp.a' cp.firstStep
    hterminal hfirst hne.symm hopen.quotient_model actor ⟨hUM hactorU,hUfirst hactorU⟩ hactorQ
  have hMX : M≤normalizer (X:Set G) := by
    change GAt Γ middle≤_
    rw [←hgen]
    exact sup_le hedgeX (zpowers_le.mpr (hUX hactorU))
  have hXQ : X≤Q := sup_le hCQ hZQ
  let Y := ⁅X,Q⁆
  have hYC : Y≤C := nine_five_commutator_join_le C Z Q C C.le_normalizer hZC
    (le_normalizer_iff_commutator_le_left.mp hQC)
    ((commutator_eq_bot_iff_le_centralizer.mpr hZcentral).le.trans bot_le)
  have hMY : M≤normalizer (Y:Set G) := by
    intro m hm
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅X,Q⁆).map (MulAut.conj m).toMonoidHom=⁅X,Q⁆
    have hxmap : X.map (MulAut.conj m).toMonoidHom=X :=
      mem_normalizer_iff_map_conj_eq.mp (hMX hm)
    have hqmap : Q.map (MulAut.conj m).toMonoidHom=Q :=
      mem_normalizer_iff_map_conj_eq.mp (hMQ hm)
    rw [map_commutator,hxmap,hqmap]
  have hYbot : Y=⊥ := middle_normal_centralizer_core_eq_bot ctx middle hpath Y
    (hYC.trans hCQ) hMY (hYC.trans hCU)
  have hXcentral : X≤centralizer (Q:Set G) := commutator_eq_bot_iff_le_centralizer.mp hYbot
  let D : Subgroup G := closure ((fun x:G=>x^2) '' (X:Set G))
  have hDC : D≤C := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x,hx,rfl⟩
    have hprod : x∈(C:Set G)*(Z:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right C Z (hCQ.trans (hQself.trans hMZ))]
      exact hx
    obtain ⟨c,hc,z,hz,hcz⟩ := hprod
    change c*z=x at hcz
    rw [←hcz]
    have hcomm : Commute c z := (hZdata z hz).2.2 c (hCQ hc)
    change (c*z)^2∈C
    rw [hcomm.mul_pow,(hZdata z hz).2.1,mul_one]
    exact C.pow_mem hc 2
  have hMD : M≤normalizer (D:Set G) := by
    change M≤normalizer (closure ((fun x:G=>x^2) '' (X:Set G)):Set G)
    rw [le_normalizer_closure_iff]
    rintro m hm _ ⟨x,hx,rfl⟩
    apply Subgroup.subset_closure
    refine ⟨MulAut.conj m x,(mem_normalizer_iff.mp (hMX hm) x).mp hx,?_⟩
    exact (map_pow (MulAut.conj m) x 2).symm
  have hDbot : D=⊥ := middle_normal_centralizer_core_eq_bot ctx middle hpath D
    (hDC.trans hCQ) hMD (hDC.trans hCU)
  have hXZ : X≤Z := by
    intro x hx
    rw [hZomega]
    apply (mem_omegaOneCenterAmbient_iff Q x).mpr
    refine ⟨hXQ hx,?_,mem_centralizer_iff.mp (hXcentral hx)⟩
    have hh : x^2∈D := Subgroup.subset_closure ⟨x,hx,rfl⟩
    have hb : x^2∈(⊥:Subgroup G) := hDbot ▸ hh
    exact Subgroup.mem_bot.mp hb
  have hZA : Z≤VAt Γ cp.firstStep :=
    nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hfirst)
  rw [←hCA]
  exact le_inf le_rfl (le_sup_left.trans (hXZ.trans hZA))

end Stellmacher.SectionTen
