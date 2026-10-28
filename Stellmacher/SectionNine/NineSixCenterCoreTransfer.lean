module

public import Stellmacher.SectionNine.NineSixResidualIntersection
public import Stellmacher.SectionNine.NineSixLengthThree
public import Stellmacher.SectionNine.NineFivePenultimateJoinAction

/-!
# A center commutator forces the neighboring core in (9.6)

Assume the first core quotient is SL₂(2), the first module has order sixteen,
and the critical path has length greater than one. For any neighbor d of
the initial vertex, an acting subgroup contained in the initial core whose
commutator with V_d is contained in the initial center must lie in Q_d.

At the first step, the actors centralize the initial center. Residual
generation writes V as that center joined with [V,E], whose full stabilizer
invariance then places the actor commutator in [V,E]. The proved residual
intersection bounds it by the first center; the genuine faithful quotient
kernel puts the actors in the first core. An initial-stabilizer neighbor
transporter preserves the initial center and core, and carries this result
to every neighboring vertex.

Source: Stellmacher (9.6), printed p.53 / PDF p.43 of
`refs/files/stellmacher-n-group.pdf`, the final alternative after the
commutator R₀ is contained in the initial center. The preterminal module's
containment in the initial core and its required commutator bound are
supplied by the separate geometric consumer.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionEight
universe u

private theorem initial_core_transfer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=16)
    (actors : Subgroup G) (hactors : actors ≤ QAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,actors⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a) :
    actors ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let D := ⁅V,E⁆
  let Z := ZAt Γ cp.a
  have hactorsP : actors ≤ P := hactors.trans
    ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans
      (edge_sylow_data ctx.sectionSeven Γ cp).2.1)
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hPE : P ≤ Subgroup.normalizer (E : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp
    change ((Γ.twoResidualAt cp.firstStep).subgroupOf P).Normal
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_normal _
  have hPD : P ≤ Subgroup.normalizer (D : Set G) := by
    intro actor hactor
    rw [Subgroup.mem_normalizer_iff_map_conj_eq,Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (stabilizer_le_normalizer_v Γ cp.firstStep hactor),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPE hactor)]
  have hZcore : Z ≤ omegaOneCenter (QAt Γ cp.a) :=
    (lemma_seven_three ctx.sectionSeven Γ).center_core _ _
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
  have hZactors : ⁅Z,actors⁆=⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((hZcore.trans ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))).trans (Subgroup.centralizer_le hactors))
  have hVP : V ≤ P :=
    (neighbor_join_le_core_of_length_gt_one Γ cp (by omega) cp.firstStep).trans (by
      change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
      rw [Γ.twoCoreAt_def]
      exact twoCoreIn_le _)
  have hZV : Z ≤ V := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hDcomm : ⁅V,actors⁆ ≤ D := by
    have hgen : V=Z ⊔ D := nine_six_initial_residual_generation ctx.toLocalContext
    conv_lhs => rw [hgen]
    exact nine_five_commutator_join_le Z D actors D
      ((hZV.trans hVP).trans hPD) Subgroup.le_normalizer
      (hZactors.le.trans bot_le)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hactorsP.trans hPD))
  have hline : ⁅V,actors⁆ ≤ ZAt Γ cp.firstStep :=
    (le_inf hcomm hDcomm).trans
      (nine_six_initial_center_residual_intersection_le_next_center ctx hb hquot hcard)
  have hkernel := (nine_next_center_commutator_and_kernel ctx hb cp.firstStep
    ⟨1,Γ.act_one _⟩).2.2
  intro actor hactor
  exact (hkernel actor (hactorsP hactor)).mp
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans hline)

public theorem nine_six_center_commutator_forces_neighbor_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=16)
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (actors : Subgroup G) (hactors : actors ≤ QAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅VAt ctx.Γ neighbor,actors⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a) :
    actors ≤ QAt ctx.Γ neighbor := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hneighbor
  have hback : Γ.act (mover:G)⁻¹ neighbor=cp.firstStep := by
    rw [← hmover,← Γ.act_mul,mul_inv_cancel,Γ.act_one]
  let equiv := MulAut.conj (mover:G)
  have hVmap : (VAt Γ neighbor).map equiv.toMonoidHom=VAt Γ cp.firstStep := by
    change (v Γ neighbor).map (MulAut.conj (mover:G)).toMonoidHom=v Γ cp.firstStep
    have hh := v_act Γ (mover:G)⁻¹ neighbor
    simpa only [inv_inv,hback] using hh.symm
  have hQmap : (QAt Γ neighbor).map equiv.toMonoidHom=QAt Γ cp.firstStep := by
    change (q Γ neighbor).map (MulAut.conj (mover:G)).toMonoidHom=q Γ cp.firstStep
    have hh := q_act Γ (mover:G)⁻¹ neighbor
    simpa only [inv_inv,hback] using hh.symm
  have hZmap : (ZAt Γ cp.a).map equiv.toMonoidHom=ZAt Γ cp.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (stabilizer_le_normalizer_z Γ cp.a mover.property)
  have hQaMap : (QAt Γ cp.a).map equiv.toMonoidHom=QAt Γ cp.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (stabilizer_le_normalizer_q Γ cp.a mover.property)
  have hactorsMap : actors.map equiv.toMonoidHom ≤ QAt Γ cp.a :=
    (Subgroup.map_mono hactors).trans_eq hQaMap
  have hcommMap : ⁅VAt Γ cp.firstStep,actors.map equiv.toMonoidHom⁆ ≤ ZAt Γ cp.a := by
    have hh := Subgroup.map_mono (f := equiv.toMonoidHom) hcomm
    rw [Subgroup.map_commutator,hVmap,hZmap] at hh
    exact hh
  apply (Subgroup.map_le_map_iff_of_injective (f := equiv.toMonoidHom) equiv.injective).mp
  rw [hQmap]
  exact initial_core_transfer ctx hb hquot hcard (actors.map equiv.toMonoidHom)
    hactorsMap hcommMap

end Stellmacher.SectionNine
