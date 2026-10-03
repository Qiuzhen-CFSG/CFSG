module
public import Stellmacher.SectionNine.NineFourCentralNormalization
public import Stellmacher.SectionNine.NineFourNormalizedEnlarged
public import Stellmacher.SectionNine.NineFourResidualSupplement
public import Stellmacher.SectionNine.DistanceOneCenterResidual
public import Stellmacher.RelativeTwoResidualCommutatorSupplement

/-!
# Residual normalization from the full fixed-subgroup decomposition

For the original normalized counterexample, suppose A is the initial
center joined with the full remote-module centralizer of its vertex core.
Then [A V_next,E_next] lies in V_next, the exact input to the final central
contradiction. No extra action or generation hypothesis is supplied.

The initial core normalizes both factors of A, and therefore A V_next.
The actor normalizes this join by the original displacement condition.
Their join L contains E_next by the established edge-core supplement.
The relative residual-supplement theorem makes O²(L) act trivially on
A V_next modulo V_next: the actor already acts trivially there and the
initial core is a two-group. Residual perfection puts E_next inside O²(L),
which gives the claimed bound.

This supplies the sentence following the full fixed-subgroup comparison
in Stellmacher (9.4), printed p.52 / PDF p.42 of
`refs/files/stellmacher-n-group.pdf`, retaining the literal ambient groups.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_central_residual_normalization
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx)
    (hremote : ctx.Γ.act data.conjugator data.remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hfullfixed : data.subgroup = ZAt ctx.Γ ctx.criticalPath.a ⊔
      (VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) ⊓ Subgroup.centralizer
        (QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Set G))) :
    ⁅data.subgroup ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,
      EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let d := Γ.act data.conjugator data.remote
  let P := GAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let Qd := QAt Γ d
  let V := VAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let A := data.subgroup
  let M := A ⊔ V
  let D := Subgroup.zpowers data.actor
  let L := Qa ⊔ D
  let F := (Qa ⊓ Qd) ⊔ D
  let E := EAt Γ cp.firstStep
  have hQaEdge : Qa ≤ GAt Γ cp.a ⊓ P :=
    (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers
  have hQaGd : Qa ≤ GAt Γ d :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a d hremote default).2.2
  have hQaZa : Qa ≤ Subgroup.normalizer (Za : Set G) :=
    hQaEdge.trans (inf_le_left.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hQaVd : Qa ≤ Subgroup.normalizer (VAt Γ d : Set G) :=
    hQaGd.trans (stabilizer_le_normalizer_v Γ d)
  have hQaQd : Qa ≤ Subgroup.normalizer (Qd : Set G) :=
    hQaGd.trans (stabilizer_le_normalizer_q Γ d)
  have hQaC : Qa ≤ Subgroup.normalizer (Subgroup.centralizer (Qd : Set G) : Set G) :=
    hQaQd.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (Qd : Set G)))
  have hQaA : Qa ≤ Subgroup.normalizer (A : Set G) := by
    rw [show A = Za ⊔ (VAt Γ d ⊓ Subgroup.centralizer (Qd : Set G)) from hfullfixed]
    exact (le_inf hQaZa ((le_inf hQaVd hQaC).trans
      Subgroup.inf_normalizer_le_normalizer_inf)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQaV : Qa ≤ Subgroup.normalizer (V : Set G) :=
    hQaEdge.trans (inf_le_right.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hQaM : Qa ≤ Subgroup.normalizer (M : Set G) :=
    (le_inf hQaA hQaV).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have haux := nine_four_auxiliary_normalization ctx hb d hremote data.actor data.actor_mem
    A data.subgroup_le data.commutator_le
  have hDM : D ≤ Subgroup.normalizer (M : Set G) := le_sup_right.trans haux.1
  have hLM : L ≤ Subgroup.normalizer (M : Set G) := sup_le hQaM hDM
  have hLP : L ≤ P := sup_le (hQaEdge.trans inf_le_right)
    (Subgroup.zpowers_le.mpr data.actor_mem)
  have hLV : L ≤ Subgroup.normalizer (V : Set G) :=
    hLP.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hb2 : 2 < cp.length := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change Odd cp.length at hodd
    obtain ⟨k,hk⟩ := hodd
    change 1 < cp.length at hb
    omega
  have hAQa : A ≤ Qa := data.subgroup_le.trans
    ((nine_seven_neighbor_module_le_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hremote)).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext hb2 cp.a))
  have hMV : M ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (hAQa.trans hQaV) V.le_normalizer
  have hQaTwo : IsPGroup 2 Qa := by
    change IsPGroup 2 (Γ.twoCoreAt cp.a)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := GAt Γ cp.a)).map _
  have hDMcomm : ⁅D,M⁆ ≤ V := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl le_sup_right).trans haux.2
  have hrescomm : ⁅twoResidualIn L,M⁆ ≤ V :=
    twoResidual_commutator_le_of_relative_two_supplement M V D Qa L
      hMV hLV hLM (sup_comm D Qa) hQaTwo hDMcomm
  have hgen := data.generates cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)))
  have hEL : E ≤ L := nine_four_residual_le_core_actor_join ctx hb data.actor
    data.actor_mem (by simpa only [inf_comm] using hgen)
  have hEeq : E = twoResidualIn P := by
    change Γ.twoResidualAt cp.firstStep = _
    exact Γ.twoResidualAt_def _
  have hresE : twoResidualIn E = E := by
    have htop : twoResidualAmbient (⊤ : Subgroup E) = ⊤ := by
      rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual,hEeq]
      exact twoResidualAmbient_has_top_twoResidual P
    have hh := map_twoResidualAmbient_of_subgroup_image
      (⊤ : Subgroup E) E.subtype E (by
        rw [← MonoidHom.range_eq_map,Subgroup.range_subtype])
    rw [htop,← MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh.symm
  have hER : E ≤ twoResidualIn L := hresE.symm.le.trans (twoResidualIn_mono E L hEL)
  rw [Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono hER le_rfl).trans hrescomm

end Stellmacher.SectionNine
