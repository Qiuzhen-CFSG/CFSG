module
public import Stellmacher.SectionNine.NineTenTerminalNormalDisplacement
public import Stellmacher.SectionNine.NineTenResidualIntersectionNoncentral
public import Stellmacher.SectionNine.NineThreeCenterSplitting

/-!
# The actual distance-five residual displacement escapes the first module

At critical length five, retain the original terminal wreath classification.
The subgroup D=O₂(E_first)∩Q_second has [V_third,D] not contained in
I=V_first∩V_third. This concerns the literal offsets of the original path.

The proved second-core residual supplement gives nontrivial D-action on I.
Since D lies in Q_first, its commutators with I lie in Z_first. The first
and third centers are disjoint, so that action remains nontrivial modulo
Z_third. Also Q_second normalizes D: it lies in G_first, which normalizes
the first residual core. Cubic two-arc transport carries the terminal,
penultimate, and backward vertices simultaneously to third, second, and
first. Pulling back D applies the terminal normal-displacement obstruction;
injective conjugation returns the claimed noncontainment.

This gives the action contradiction required in Stellmacher (9.10)(12),
printed p.59, directly from the actual classification (6), without the
stronger edge-generation assertion (10) as a premise.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_five_residual_core_displacement_not_le_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 5)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3) :
    let second := ctx.criticalPath.path ⟨2,by omega⟩
    let third := ctx.criticalPath.path ⟨3,by omega⟩
    ¬ ⁅VAt ctx.Γ third,
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ⊓ QAt ctx.Γ second⁆ ≤
        VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length=5 := hb
  have hshort : 1<cp.length := by omega
  let second := cp.path ⟨2,by omega⟩
  let third := cp.path ⟨3,by omega⟩
  let first := cp.firstStep
  let R := twoCoreIn (EAt Γ first)
  let D := R ⊓ QAt Γ second
  let I := VAt Γ first ⊓ VAt Γ third
  change ¬ ⁅VAt Γ third,D⁆≤I
  have hleft : Γ.adjacent second first := by
    have hedge := cp.path_adj ⟨1,by omega⟩
    change Γ.adjacent (cp.path ⟨1,by omega⟩) second at hedge
    rw [cp.path_first] at hedge
    exact Γ.adjacent_symm hedge
  have hright : Γ.adjacent second third := cp.path_adj ⟨2,by omega⟩
  have hdistinct : first≠third := by
    have hh := nine_seven_path_vertices_ne Γ cp 1 3 (by omega) (by omega)
    rwa [cp.path_first] at hh
  obtain ⟨middleMover,hmiddleMover⟩ :=
    (lemma_seven_one ctx.sectionSeven Γ).local_transitivity first
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft))
  have hmiddleOrbit : IsConjugateVertex Γ cp.a second := ⟨middleMover,hmiddleMover⟩
  have hRfirst : R≤QAt Γ first := by
    change twoCoreIn (Γ.twoResidualAt first)≤Γ.twoCoreAt first
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hcommFirst : ⁅I,D⁆≤ZAt Γ first :=
    (Subgroup.commutator_mono inf_le_left
      ((show D≤R from inf_le_left).trans hRfirst)).trans_eq
        (nine_next_center_commutator_and_kernel ctx hshort first ⟨1,Γ.act_one _⟩).2.1
  have hdisjoint := (nine_three_center_split ctx hshort hmiddleOrbit
    hleft hright hdistinct).2.1
  have hnontrivial : ¬ ⁅I,D⁆≤ZAt Γ third := by
    intro hle
    have hzero : ⁅I,D⁆=⊥ := le_bot_iff.mp
      (hdisjoint.eq_bot ▸ le_inf hcommFirst hle)
    have hnonzero := nine_ten_five_residual_core_intersection_noncentral
      ctx hb hcard hmodel hinter
    change ⁅D,I⁆≠⊥ at hnonzero
    exact hnonzero (Subgroup.commutator_comm D I ▸ hzero)
  have hRnormal : GAt Γ first≤Subgroup.normalizer (R:Set G) := by
    let Pf := GAt Γ first
    let Ef := EAt Γ first
    have hEf : Ef=twoResidualIn Pf := Γ.twoResidualAt_def first
    have hEP : Ef≤Pf := hEf ▸ twoResidualIn_le Pf
    have hRP : R≤Pf := (twoCoreIn_le Ef).trans hEP
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal Ef Pf hEP (hEf ▸ twoResidualIn_normal Pf))
  have hQfirst : QAt Γ second≤GAt Γ first :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core second first
      ((mem_neighborhood_iff_adjacent Γ).mpr hleft) default).2.2
  have hDnormal : QAt Γ second≤Subgroup.normalizer (D:Set G) := by
    intro q hq
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hRnormal (hQfirst hq),(QAt Γ second).le_normalizer hq⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let Iterminal := VAt Γ cp.a' ⊓ VAt Γ preterminal
  obtain ⟨alignment,halign,_⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  change Γ.act alignment cp.a=penultimate at halign
  have hpenOrbit : IsConjugateVertex Γ penultimate second := by
    refine ⟨alignment⁻¹*(middleMover:G),?_⟩
    have hinverse : Γ.act alignment⁻¹ penultimate=cp.a := by
      rw [←halign,←Γ.act_mul,mul_inv_cancel,Γ.act_one]
    rw [Γ.act_mul,hinverse]
    exact hmiddleMover
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreAdj := Γ.adjacent_symm (nine_five_previous_adjacent_penultimate
    ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩)
  have hterminalNe : cp.a'≠preterminal :=
    (nine_five_previous_ne_terminal ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩).symm
  obtain ⟨mover,hmoveLeft,hmoveMiddle,hmoveRight⟩ := nine_seven_two_arc_transport
    ctx.sectionSeven Γ hterminalAdj hpreAdj hterminalNe hright hleft hdistinct.symm
      hpenOrbit (lemma_nine_three_ambient ctx hshort second hmiddleOrbit).1
  change Γ.act mover cp.a'=third at hmoveLeft
  change Γ.act mover penultimate=second at hmoveMiddle
  change Γ.act mover preterminal=first at hmoveRight
  let equiv := MulAut.conj mover⁻¹
  let f := equiv.toMonoidHom
  have hVmap : (VAt Γ cp.a').map f=VAt Γ third := by rw [←v_act,hmoveLeft]
  have hVpreMap : (VAt Γ preterminal).map f=VAt Γ first := by rw [←v_act,hmoveRight]
  have hQmap : (QAt Γ penultimate).map f=QAt Γ second := by rw [←q_act,hmoveMiddle]
  have hZmap : (ZAt Γ cp.a').map f=ZAt Γ third := by rw [←z_act,hmoveLeft]
  have hImap : Iterminal.map f=I := by
    rw [Subgroup.map_inf _ _ _ equiv.injective,hVmap,hVpreMap,inf_comm]
  let Dback := D.comap f
  have hDmap : Dback.map f=D := Subgroup.map_comap_eq_self_of_surjective equiv.surjective D
  have hbackCore : Dback≤QAt Γ penultimate := by
    apply (Subgroup.map_le_map_iff_of_injective (f:=f) equiv.injective).mp
    rw [hDmap,hQmap]
    exact inf_le_right
  have hbackNormal : QAt Γ penultimate≤Subgroup.normalizer (Dback:Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro q hq d hd
    change f (q*d*q⁻¹)∈D
    rw [map_mul,map_mul,map_inv]
    exact Subgroup.le_normalizer_iff.mp hDnormal (f q)
      (hQmap ▸ Subgroup.mem_map_of_mem f hq) (f d) hd
  have hbackNontrivial : ¬ ⁅Iterminal,Dback⁆≤ZAt Γ cp.a' := by
    intro hle
    apply hnontrivial
    have hh := Subgroup.map_mono (f:=f) hle
    rwa [Subgroup.map_commutator,hImap,hDmap,hZmap] at hh
  have hback := nine_ten_terminal_normal_subgroup_displacement_not_le_intersection
    ctx (by omega) hcard hmodel hinter Dback hbackCore hbackNormal hbackNontrivial
  intro hle
  apply hback
  apply (Subgroup.map_le_map_iff_of_injective (f:=f) equiv.injective).mp
  rw [Subgroup.map_commutator,hVmap,hDmap,hImap]
  exact hle

end Stellmacher.SectionNine
