module
public import Stellmacher.SectionNine.NineFourCentralNormalization
public import Stellmacher.SectionNine.NineFourReduction
public import Stellmacher.SectionNine.NineSevenShiftedIntersections
public import Theory.GroupAction.CyclicDisplacementRelIndex

/-!
# The auxiliary-module index estimate in (9.4)

For a selected element y of the elementary abelian remote module, the subgroup
`V_y = [⟨y⟩ V_next, Q] Z_next` has index at most two over
its intersection with the remote module. The displacement map from the
auxiliary group Q to `V_next/(V_next ∩ V_remote)` kills `Q ∩ Q_a`: the
initial core fixes the remote vertex and therefore normalizes its module.
The auxiliary-core geometry bounds the kernel index by two. The image
contains every commutator defining V_y, giving the required cardinal bound.
The displacement algebra is shared through `Subgroup.cyclic_displacement_relIndex_le`.
Only adjacency, distance two, and the original commutator containment are
needed; the counterexample and enlargement assumptions are unnecessary.

This is the source estimate (9.4)(3), printed p.51/PDF p.41 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u

set_option maxHeartbeats 800000

public theorem nine_four_auxiliary_intersection_index
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (A : Subgroup G) (hA : A ≤ VAt ctx.Γ remote)
    (hcomm : ⁅A, Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep)
    (y : G) (hy : y ∈ A) :
    let F := (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote) ⊔
      Subgroup.zpowers actor
    let Q := twoCoreIn (twoResidualIn F)
    let V_y := ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep, Q⁆ ⊔
      ZAt ctx.Γ ctx.criticalPath.firstStep
    Nat.card V_y ≤ 2 * Nat.card
      (V_y ⊓ VAt ctx.Γ remote : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let D := VAt Γ remote
  let U := VAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let Qd := QAt Γ remote
  let R := Qa ⊓ Qd
  let C := Subgroup.zpowers actor
  let F := R ⊔ C
  let Q := twoCoreIn (twoResidualIn F)
  let W := ⁅Subgroup.zpowers y ⊔ U, Q⁆ ⊔ ZAt Γ cp.firstStep
  let _ : IsElementaryAbelian 2 D := nine_four_remote_elementary
    ctx.toLocalContext hb remote hdistance
  let _ : IsElementaryAbelian 2 U :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hcenter := nine_seven_center_join ctx cp.a ⟨1, Γ.act_one _⟩
  have hfirstMem : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hnextZa : ZAt Γ cp.firstStep ≤ ZAt Γ cp.a :=
    (hcenter.2 cp.firstStep hfirstMem).2
  have hremoteAdj : Γ.adjacent remote cp.a :=
    Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)
  have hZaD : ZAt Γ cp.a ≤ D := by
    exact nine_seven_neighbor_center_le_module Γ hremoteAdj
  have hZD : ZAt Γ cp.firstStep ≤ D := hnextZa.trans hZaD
  have hZU : ZAt Γ cp.firstStep ≤ U := hnextZa.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hgeom := nine_four_auxiliary_core_geometry ctx hb remote actor hactor
  have hQnext : Q ≤ QAt Γ cp.firstStep := hgeom.2.1
  have hQF : Q ≤ F := (twoCoreIn_le _).trans (twoResidualIn_le _)
  have hnextComm : ⁅U, QAt Γ cp.firstStep⁆ = ZAt Γ cp.firstStep :=
    (nine_next_center_commutator_and_kernel ctx hb cp.firstStep
      ⟨1, Γ.act_one _⟩).2.1
  have hQ : ⁅U, Q⁆ ≤ ZAt Γ cp.firstStep := by
    rw [← hnextComm]
    exact Subgroup.commutator_mono le_rfl hQnext
  have hyD : y ∈ D := hA hy
  have hCy : Subgroup.zpowers y ≤ D := Subgroup.zpowers_le.mpr hyD
  have hCyA : Subgroup.zpowers y ≤ A := Subgroup.zpowers_le.mpr hy
  have hCyComm : ⁅Subgroup.zpowers y, C⁆ ≤ U :=
    (Subgroup.commutator_mono hCyA le_rfl).trans hcomm
  have hnorm := nine_four_auxiliary_normalization ctx hb remote hremote actor hactor
    (Subgroup.zpowers y) hCy hCyComm
  have hcommNorm : ⁅Subgroup.zpowers y ⊔ U, Q⁆ ≤ U :=
    (Subgroup.commutator_mono le_rfl hQF).trans hnorm.2
  have hQaGd : Qa ≤ GAt Γ remote :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a remote hremote default).2.2
  have hQaD : Qa ≤ Subgroup.normalizer D :=
    hQaGd.trans (stabilizer_le_normalizer_v Γ remote)
  have hR : ∀ q ∈ Q ⊓ Qa, ⁅q,y⁆ ∈ D := by
    intro q hq
    have hbound : ⁅Qa, D⁆ ≤ D := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp hQaD
    exact hbound (Subgroup.commutator_mem_commutator hq.2 hyD)
  have hb2 : 2 < cp.length := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change Odd cp.length at hodd
    obtain ⟨k, hk⟩ := hodd
    change 1 < cp.length at hb
    omega
  have hDQa : D ≤ Qa :=
    (nine_seven_neighbor_module_le_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hremote)).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext hb2 cp.a)
  have hQaGn : Qa ≤ GAt Γ cp.firstStep :=
    ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans
      cp.S_le_edge_stabilizers).trans inf_le_right
  have hyNorm : y ∈ Subgroup.normalizer U :=
    stabilizer_le_normalizer_v Γ cp.firstStep (hQaGn (hDQa hyD))
  have hindex : (U ⊓ D).relIndex W ≤ Qa.relIndex Q :=
    Subgroup.cyclic_displacement_relIndex_le U (ZAt Γ cp.firstStep) D Q Qa y
      (elemPow_eq_one_of_isElementaryAbelian y hyD) hyNorm hZU hZD hQ hcommNorm hR
  have hsmall : Qa.relIndex Q ≤ 2 := hgeom.2.2.1
  have hWU : W ≤ U := sup_le hcommNorm hZU
  have hIeq : (U ⊓ D) ⊓ W = W ⊓ D := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans hWU) inf_le_right) inf_le_left
  have hidx : (W ⊓ D).relIndex W ≤ 2 := by
    rw [← hIeq, Subgroup.inf_relIndex_right]
    exact hindex.trans hsmall
  have hcount := ((W ⊓ D).subgroupOf W).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show W ⊓ D ≤ W from inf_le_left)).toEquiv] at hcount
  change (W ⊓ D).relIndex W * Nat.card (W ⊓ D : Subgroup G) = Nat.card W at hcount
  change Nat.card W ≤ 2 * Nat.card (W ⊓ D : Subgroup G)
  rw [← hcount]
  exact Nat.mul_le_mul_right _ hidx

end Stellmacher.SectionNine
