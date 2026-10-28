module
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Theory.GroupAction.CardTwoDisplacementInvolution
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# The literal transvection actor in a next-orbit quotient

For a next-orbit vertex at critical distance greater than one, a local
actor satisfying |[V,t]Z/Z|=2 induces an involution with order-two total
displacement on the literal quotient V/Z. The action, its conjugation
formula, and its exact two-core kernel are retained together. No order
assumption is made on the original local element.

The quotient-conjugation image formula identifies the action displacement
with the image of the ambient commutator. Normality of the center in V and
the subgroup index formula turn the displayed source cardinality into
order two for that image. Its unique nonidentity displacement point is
fixed, so the induced automorphism squares to one. Its nontrivial
displacement excludes the identity.

Source: Stellmacher (9.4)(iii) and the transvection step before equations
(1)–(2), printed pp.50–51/PDF pp.40–41 of
`refs/files/stellmacher-n-group.pdf`. This supplies the exact order-two
actor needed for (1.7) on the next-neighbor quotient module.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem relative_index_of_quotient_card
    {G : Type*} [Group G] [Finite G] (U Z C : Subgroup G)
    (hZU : Z ≤ U) (hCU : C ≤ U) (hN : (Z.subgroupOf U).Normal)
    (hcard : QuotientCardEq (C ⊔ Z) Z 2) : Z.relIndex C = 2 := by
  let _ := hN
  have hsup : C ⊔ Z ≤ U := sup_le hCU hZU
  have hindex : Z.relIndex (C ⊔ Z) = 2 := by
    have hmul := (Z.subgroupOf (C ⊔ Z)).index_mul_card
    have hZcard : Nat.card (Z.subgroupOf (C ⊔ Z)) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ C ⊔ Z from le_sup_right)).toEquiv
    rw [hZcard] at hmul
    change Z.relIndex (C ⊔ Z) * Nat.card Z = Nat.card (C ⊔ Z : Subgroup G) at hmul
    unfold QuotientCardEq at hcard
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hmul.trans hcard)
  have heq := Subgroup.relIndex_sup_right (C.subgroupOf U) (Z.subgroupOf U)
  rw [← Subgroup.subgroupOf_sup hCU hZU, Subgroup.relIndex_subgroupOf hsup,
    Subgroup.relIndex_subgroupOf hCU] at heq
  exact heq ▸ hindex

public theorem nine_next_transvection_actor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex)
    (actor : GAt ctx.Γ vertex)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ vertex, Subgroup.zpowers (actor : G)⁆ ⊔ ZAt ctx.Γ vertex)
      (ZAt ctx.Γ vertex) 2) :
    ∃ hN : ((ZAt ctx.Γ vertex).subgroupOf (VAt ctx.Γ vertex)).Normal,
      let _ := hN
      let P := GAt ctx.Γ vertex
      let U := VAt ctx.Γ vertex
      let Z := ZAt ctx.Γ vertex
      ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
      let _ := hW
      ∃ action : P →* MulAut (U ⧸ Z.subgroupOf U),
        (∀ mover : P, ∀ point : U,
          action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
            QuotientGroup.mk' (Z.subgroupOf U)
              ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
                (Subgroup.mem_normalizer_iff.mp
                  (stabilizer_le_normalizer_v ctx.Γ vertex mover.property) point).mp
                    point.property⟩) ∧
        action.ker = pCore 2 P ∧
        _root_.IsInvolution (action actor) ∧
        Nat.card (Subgroup.zpowers (action actor)) = 2 ∧
        Nat.card (commutatorAction (Subgroup.zpowers (action actor))
          (U ⧸ Z.subgroupOf U)) = 2 := by
  obtain ⟨hN, hW, action, haction, hkernel⟩ :=
    nine_next_quotient_conjugation_action ctx hb vertex horbit
  let _ := hN
  let _ := hW
  let P := GAt ctx.Γ vertex
  let U := VAt ctx.Γ vertex
  let Z := ZAt ctx.Γ vertex
  let D := Subgroup.zpowers (actor : G)
  have hDP : D ≤ P := Subgroup.zpowers_le.mpr actor.property
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v ctx.Γ vertex
  have hcomm := (nine_next_center_commutator_and_kernel ctx hb vertex horbit).2.1
  have hQP : QAt ctx.Γ vertex ≤ P := by
    change ctx.Γ.twoCoreAt vertex ≤ P
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZU : Z ≤ U := by
    change ZAt ctx.Γ vertex ≤ U
    rw [← hcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU)
  have hCU : ⁅U, D⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hDP.trans hPU)
  have hrelative : Z.relIndex ⁅U, D⁆ = 2 :=
    relative_index_of_quotient_card U Z ⁅U, D⁆ hZU hCU hN hindex
  have hinternal : D.subgroupOf P = Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hDP, MonoidHom.map_zpowers]
    rfl
  have hrank := Subgroup.quotient_conjugation_commutatorAction_card
    P U Z D hPU hDP hN action haction
  rw [hinternal, MonoidHom.map_zpowers] at hrank
  have hrankTwo := hrank.trans hrelative
  have hinvolution := isInvolution_of_card_two_displacement (action actor) hrankTwo
  refine ⟨hN, hW, action, haction, hkernel, hinvolution, ?_, hrankTwo⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hinvolution.2 hinvolution.1]

end Stellmacher.SectionNine
