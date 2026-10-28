module

public import Stellmacher.SectionNine.NineSixResidualIntersection
public import Stellmacher.SectionNine.NineSixSmallModule
public import Stellmacher.SectionEight.GeneratedEightSixNextCoreResidual
public import Stellmacher.SectionNine.NineFivePenultimateJoinAction

/-!
# The length-three case of Stellmacher (9.6)

The initial residual-generation identity is public for the later zero
backward-commutator branch of the same source argument.

For an ambient Section Nine critical path of length three, the literal
SL₂(2) first core quotient forces the index-two intersection asserted in
(9.6). The original offset-three witness is retained.

If the index were not two, the small-module reduction gives module order
sixteen and identifies the endpoint-module intersection with the middle
center. Endpoint alignment transports the proved residual-intersection
bound to the terminal edge. Residual generation writes the terminal module
as the join of the middle center and its residual commutator. The first
module centralizes that center and normalizes the residual commutator;
therefore the mutual commutator belongs to the residual intersection and
hence to the terminal center. The faithful quotient action then puts the
first module in the terminal core, contradicting criticality.

Source: Stellmacher (9.6), printed p.53 / PDF p.43 of
`refs/files/stellmacher-n-group.pdf`, the length-three paragraph.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionEight
universe u

public theorem nine_six_initial_residual_generation
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    VAt ctx.Γ ctx.criticalPath.firstStep = ZAt ctx.Γ ctx.criticalPath.a ⊔
      ⁅VAt ctx.Γ ctx.criticalPath.firstStep, EAt ctx.Γ ctx.criticalPath.firstStep⁆ := by
  have hedge := edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath
  have hback : ctx.criticalPath.a ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
  apply eight_six_closure_eq_seed_sup_residual_commutator _
    (GAt ctx.Γ ctx.criticalPath.firstStep) _ T
  · change ctx.Γ.twoResidualAt _ ≤ ctx.Γ.vertexStabilizer _
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  · exact hedge.2.1
  · change ((ctx.Γ.twoResidualAt _).subgroupOf (ctx.Γ.vertexStabilizer _)).Normal
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_normal _
  · change ctx.Γ.twoResidualAt _ ⊔ T = ctx.Γ.vertexStabilizer _
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_sup_sylow hedge.2
  · exact hedge.1.1.trans (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a)
  · exact (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1
  · exact stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
  · exact eight_six_neighbor_join_eq_conjugate_closure ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a hback

public theorem nine_six_index_two_of_length_three
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 3)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2 := by
  classical
  by_contra hnot
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hb : 1 < cp.length := by dsimp [cp]; omega
  let pen := cp.path ⟨cp.length - 1, by omega⟩
  have hpenOffset : IsCriticalPathOffset Γ cp 2 pen :=
    ⟨⟨cp.length - 1, by omega⟩, by dsimp [cp]; omega, rfl⟩
  have hthird : third = cp.a' := by
    obtain ⟨index, hindex, rfl⟩ := hpath
    rw [← cp.path_end]
    apply congrArg cp.path
    apply Fin.ext
    dsimp [cp] at *
    omega
  have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1,Γ.act_one _⟩).2
  have hbound := nine_six_first_module_card_le ctx.toLocalContext hb hfour hquot
  have hcard := nine_six_order_sixteen_of_not_index_two ctx.toLocalContext
    pen third hpenOffset hpath hfour hbound hnot
  have hinter := nine_six_intersection_eq_center_of_not_index_two ctx.toLocalContext
    pen third hpenOffset hpath hfour hbound hnot
  change VAt Γ cp.firstStep ⊓ VAt Γ third = ZAt Γ pen at hinter
  rw [hthird] at hinter
  let W := VAt Γ cp.firstStep
  let V := VAt Γ cp.a'
  let Z := ZAt Γ pen
  let P := GAt Γ cp.a'
  let E := EAt Γ cp.a'
  let D := ⁅V,E⁆
  have hWP : W ≤ P := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2
  have hVF : V ≤ GAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hRV : ⁅V,W⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hWP.trans (stabilizer_le_normalizer_v Γ cp.a'))
  have hRW : ⁅V,W⁆ ≤ W := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hVF.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hRZ : ⁅V,W⁆ ≤ Z := (le_inf hRW hRV).trans_eq hinter
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.a' ≤ Γ.vertexStabilizer cp.a'
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hPE : P ≤ Subgroup.normalizer (E : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp
    change ((Γ.twoResidualAt cp.a').subgroupOf P).Normal
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_normal _
  have hPD : P ≤ Subgroup.normalizer (D : Set G) := by
    intro actor hactor
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (stabilizer_le_normalizer_v Γ cp.a' hactor),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPE hactor)]
  obtain ⟨actor, hpen, hend⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  let equiv := MulAut.conj actor⁻¹
  have hZmap : (ZAt Γ cp.a).map equiv.toMonoidHom = Z := by
    change (z Γ cp.a).map (MulAut.conj actor⁻¹).toMonoidHom = z Γ pen
    rw [← z_act, hpen]
  have hVmap : (VAt Γ cp.firstStep).map equiv.toMonoidHom = V := by
    change (v Γ cp.firstStep).map (MulAut.conj actor⁻¹).toMonoidHom = v Γ cp.a'
    rw [← v_act, hend]
  have hLmap : (ZAt Γ cp.firstStep).map equiv.toMonoidHom = ZAt Γ cp.a' := by
    change (z Γ cp.firstStep).map (MulAut.conj actor⁻¹).toMonoidHom = z Γ cp.a'
    rw [← z_act, hend]
  have hEmap : (EAt Γ cp.firstStep).map equiv.toMonoidHom = E := by
    change (Γ.twoResidualAt cp.firstStep).map equiv.toMonoidHom = Γ.twoResidualAt cp.a'
    rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def, ← twoResidualIn_map_equiv]
    change twoResidualIn (conjugateBy (stabilizer Γ cp.firstStep) actor⁻¹) =
      twoResidualIn (stabilizer Γ cp.a')
    rw [← stabilizer_act, hend]
  have hDmap : (⁅VAt Γ cp.firstStep, EAt Γ cp.firstStep⁆).map equiv.toMonoidHom = D := by
    rw [Subgroup.map_commutator, hVmap, hEmap]
  have hgen : V = Z ⊔ D := by
    have hh := congrArg (fun subgroup : Subgroup G => subgroup.map equiv.toMonoidHom)
      (nine_six_initial_residual_generation ctx.toLocalContext)
    change (VAt Γ cp.firstStep).map equiv.toMonoidHom =
      (ZAt Γ cp.a ⊔ ⁅VAt Γ cp.firstStep,EAt Γ cp.firstStep⁆).map equiv.toMonoidHom at hh
    rwa [Subgroup.map_sup, hVmap, hZmap, hDmap] at hh
  have hZD : Z ⊓ D ≤ ZAt Γ cp.a' := by
    have hh := Subgroup.map_mono (f := equiv.toMonoidHom)
      (nine_six_initial_center_residual_intersection_le_next_center ctx hb hquot hcard)
    change (ZAt Γ cp.a ⊓ ⁅VAt Γ cp.firstStep,EAt Γ cp.firstStep⁆).map
      equiv.toMonoidHom ≤ (ZAt Γ cp.firstStep).map equiv.toMonoidHom at hh
    rwa [Subgroup.map_inf _ _ _ equiv.injective, hZmap, hDmap, hLmap] at hh
  have hWcore : W ≤ QAt Γ pen := (nine_three_initial_extraction_inputs
    ctx.toLocalContext hb).2.1
  have hadj : Γ.adjacent pen cp.a' := nine_five_penultimate_adjacent ctx.toLocalContext
  have hZcore : Z ≤ omegaOneCenter (QAt Γ pen) :=
    (lemma_seven_three ctx.sectionSeven Γ).center_core _ _
      ((mem_neighborhood_iff_adjacent Γ).mpr hadj)
  have hZW : ⁅Z,W⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((hZcore.trans ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))).trans (Subgroup.centralizer_le hWcore))
  have hZV : Z ≤ V := hgen ▸ le_sup_left
  have hDV : D ≤ V := hgen ▸ le_sup_right
  have hVP : V ≤ P :=
    (neighbor_join_le_core_of_length_gt_one Γ cp (by omega) cp.a').trans (by
      change Γ.twoCoreAt cp.a' ≤ Γ.vertexStabilizer cp.a'
      rw [Γ.twoCoreAt_def]
      exact twoCoreIn_le _)
  have hRD : ⁅V,W⁆ ≤ D := by
    conv_lhs => rw [hgen]
    exact nine_five_commutator_join_le Z D W D
      ((hZV.trans hVP).trans hPD) Subgroup.le_normalizer
      (hZW.le.trans bot_le)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hWP.trans hPD))
  have hRline : ⁅V,W⁆ ≤ ZAt Γ cp.a' := (le_inf hRZ hRD).trans hZD
  have hkernel := (nine_next_center_commutator_and_kernel ctx hb cp.a'
    ⟨actor,hend⟩).2.2
  have hWQ : W ≤ QAt Γ cp.a' := by
    intro point hpoint
    exact (hkernel point (hWP hpoint)).mp
      ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hpoint)).trans hRline)
  exact cp.critical.2
    ((lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1.trans hWQ)

end Stellmacher.SectionNine
