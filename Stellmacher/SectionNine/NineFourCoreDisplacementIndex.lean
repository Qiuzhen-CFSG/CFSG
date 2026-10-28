module
public import Stellmacher.SectionNine.NineFourAuxiliaryIndex

/-!
# The source-(3) displacement bound for any next-core subgroup

For a normalized remote neighbor at distance two from the next vertex,
let Q be any subgroup of the next core and let y belong to the remote
module. If [⟨y⟩V_next,Q] lies in V_next, the literal subgroup obtained
by adjoining Z_next has index at most two over its remote intersection.
No auxiliary F or residual action is assumed.

The shared displacement homomorphism modulo V_next intersect V_remote
kills Q intersect Q_a: the initial core normalizes the remote module.
The initial edge-core calculation bounds Q_a's relative index in every
next-core subgroup by two. Index-times-cardinality gives the conclusion.

This is Stellmacher (9.4)(3), printed p.51, in a form also applying to
O₂(E_next) in the final central paragraph on printed p.52 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement IsMulCommutative
universe u

public theorem nine_four_core_displacement_index
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2)
    (Q : Subgroup G) (hQnext : Q ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (y : G) (hyD : y ∈ VAt ctx.Γ remote)
    (hcomm : ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,Q⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep) :
    let W := ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,Q⁆ ⊔
      ZAt ctx.Γ ctx.criticalPath.firstStep
    Nat.card W ≤ 2 * Nat.card (W ⊓ VAt ctx.Γ remote : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let D := VAt Γ remote
  let U := VAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let W := ⁅Subgroup.zpowers y ⊔ U,Q⁆ ⊔ ZAt Γ cp.firstStep
  let _ : IsElementaryAbelian 2 D := nine_four_remote_elementary
    ctx.toLocalContext hb remote hdistance
  let _ : IsElementaryAbelian 2 U :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hcenter := nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩
  have hnextZa : ZAt Γ cp.firstStep ≤ ZAt Γ cp.a :=
    (hcenter.2 cp.firstStep ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2
  have hZaD : ZAt Γ cp.a ≤ D := nine_seven_neighbor_center_le_module Γ
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote))
  have hZD : ZAt Γ cp.firstStep ≤ D := hnextZa.trans hZaD
  have hZU : ZAt Γ cp.firstStep ≤ U := hnextZa.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hQ : ⁅U,Q⁆ ≤ ZAt Γ cp.firstStep :=
    (Subgroup.commutator_mono le_rfl hQnext).trans_eq
      (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1,Γ.act_one _⟩).2.1
  have hQaGd : Qa ≤ GAt Γ remote :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a remote hremote default).2.2
  have hQaD : Qa ≤ Subgroup.normalizer D := hQaGd.trans (stabilizer_le_normalizer_v Γ remote)
  have hR : ∀ q ∈ Q ⊓ Qa, ⁅q,y⁆ ∈ D := by
    intro q hq
    have hbound : ⁅Qa,D⁆ ≤ D := Subgroup.le_normalizer_iff_commutator_le_right.mp hQaD
    exact hbound (Subgroup.commutator_mem_commutator hq.2 hyD)
  have hb2 : 2 < cp.length := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change Odd cp.length at hodd
    obtain ⟨k,hk⟩ := hodd
    change 1 < cp.length at hb
    omega
  have hDQa : D ≤ Qa :=
    (nine_seven_neighbor_module_le_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hremote)).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext hb2 cp.a)
  have hQaEdge : Qa ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers
  have hyNorm : y ∈ Subgroup.normalizer U :=
    stabilizer_le_normalizer_v Γ cp.firstStep ((hQaEdge (hDQa hyD)).2)
  have hindex : (U ⊓ D).relIndex W ≤ Qa.relIndex Q :=
    Subgroup.cyclic_displacement_relIndex_le U (ZAt Γ cp.firstStep) D Q Qa y
      (elemPow_eq_one_of_isElementaryAbelian y hyD) hyNorm hZU hZD hQ hcomm hR
  have hsmall : Qa.relIndex Q ≤ 2 := by
    let edge := GAt Γ cp.a ⊓ GAt Γ cp.firstStep
    have hcount := (Qa.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQaEdge).toEquiv] at hcount
    have hQaIndex : Qa.relIndex edge = 2 :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos
        (hcount.trans (nine_initial_edge_core_product ctx hb).2)
    rw [← hQaIndex]
    exact Subgroup.relIndex_le_of_le_right
      (hQnext.trans ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans
        cp.S_le_edge_stabilizers)) Subgroup.index_ne_zero_of_finite
  have hWU : W ≤ U := sup_le hcomm hZU
  have hIeq : (U ⊓ D) ⊓ W = W ⊓ D := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans hWU) inf_le_right) inf_le_left
  have hidx : (W ⊓ D).relIndex W ≤ 2 := by
    rw [← hIeq,Subgroup.inf_relIndex_right]
    exact hindex.trans hsmall
  have hcount := ((W ⊓ D).subgroupOf W).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show W ⊓ D ≤ W from inf_le_left)).toEquiv] at hcount
  change (W ⊓ D).relIndex W * Nat.card (W ⊓ D : Subgroup G) = Nat.card W at hcount
  change Nat.card W ≤ 2 * Nat.card (W ⊓ D : Subgroup G)
  rw [← hcount]
  exact Nat.mul_le_mul_right _ hidx

end Stellmacher.SectionNine
