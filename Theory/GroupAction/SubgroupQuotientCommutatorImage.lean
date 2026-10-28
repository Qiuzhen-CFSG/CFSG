module

public import Theory.GroupAction.SubgroupQuotientFullAction
public import Mathlib.GroupTheory.Index

/-!
# Exact displacement images for subgroup quotient actions

For a prescribed quotient-conjugation action, its displacement subgroup
is the image of the ambient subgroup commutator. This retains the actual
quotient rather than replacing it by an abstract isomorphic module.
-/

namespace Subgroup
open scoped commutatorElement

public theorem quotient_conjugation_commutatorAction_eq_image
    {G : Type*} [Group G] (P Q C D : Subgroup G)
    (hPQ : P ≤ normalizer (Q : Set G)) (hDP : D ≤ P)
    (hC : (C.subgroupOf Q).Normal) :
    let _ := hC
    ∀ action : P →* MulAut (Q ⧸ C.subgroupOf Q),
      (∀ actor : P, ∀ point : Q,
        action actor (QuotientGroup.mk' (C.subgroupOf Q) point) =
          QuotientGroup.mk' (C.subgroupOf Q)
            ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
              (mem_normalizer_iff.mp (hPQ actor.property) point).mp point.property⟩) →
      commutatorAction ((D.subgroupOf P).map action) (Q ⧸ C.subgroupOf Q) =
        (⁅Q, D⁆.subgroupOf Q).map (QuotientGroup.mk' (C.subgroupOf Q)) := by
  let _ := hC
  dsimp only
  intro action haction
  let projection := QuotientGroup.mk' (C.subgroupOf Q)
  let actors := (D.subgroupOf P).map action
  let displacement := commutatorAction actors (Q ⧸ C.subgroupOf Q)
  apply le_antisymm
  · rw [commutatorAction_eq_closure]
    rw [closure_le]
    rintro _ ⟨actor, point, rfl⟩
    obtain ⟨representative, hrepresentative, heq⟩ := actor.property
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Q) point
    change (projection lift)⁻¹ *
      (actor : MulAut (Q ⧸ C.subgroupOf Q)) (projection lift) ∈ _
    rw [← heq, haction, ← map_inv, ← map_mul]
    apply mem_map_of_mem
    change (lift : G)⁻¹ * ((representative : G) * (lift : G) *
      (representative : G)⁻¹) ∈ ⁅Q, D⁆
    simpa only [commutatorElement_def, inv_inv, mul_assoc, coe_subtype] using
      commutator_mem_commutator (Q.inv_mem lift.property) hrepresentative
  · let preimage := (displacement.comap projection).map Q.subtype
    have hbound : ⁅Q, D⁆ ≤ preimage := by
      apply commutator_le.mpr
      intro point hpoint actor hactor
      let pointQ : Q := ⟨point, hpoint⟩
      let actorP : P := ⟨actor, hDP hactor⟩
      let actorImage : actors := ⟨action actorP, mem_map_of_mem action hactor⟩
      have hcommQ : ⁅point, actor⁆ ∈ Q :=
        (le_normalizer_iff_commutator_le_left.mp (hDP.trans hPQ))
          (commutator_mem_commutator hpoint hactor)
      refine ⟨⟨⁅point, actor⁆, hcommQ⟩, ?_, rfl⟩
      change projection ⟨⁅point, actor⁆, hcommQ⟩ ∈ displacement
      have hmem : (projection pointQ⁻¹)⁻¹ * (actorImage • projection pointQ⁻¹) ∈
          displacement := by
        dsimp only [displacement]
        rw [commutatorAction_eq_closure]
        exact subset_closure ⟨actorImage, projection pointQ⁻¹, rfl⟩
      have heq : (projection pointQ⁻¹)⁻¹ * (actorImage • projection pointQ⁻¹) =
          projection ⟨⁅point, actor⁆, hcommQ⟩ := by
        change (projection pointQ⁻¹)⁻¹ * action actorP (projection pointQ⁻¹) = _
        rw [haction, ← map_inv, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [coe_mul, coe_inv, inv_inv, commutatorElement_def, pointQ, actorP,
          mul_assoc]
      exact heq ▸ hmem
    rintro point ⟨representative, hrepresentative, rfl⟩
    obtain ⟨lift, hlift, heq⟩ := hbound hrepresentative
    have heq' : lift = representative := Subtype.ext heq
    exact heq' ▸ hlift

public theorem quotient_conjugation_commutatorAction_card
    {G : Type*} [Group G] [Finite G] (P Q C D : Subgroup G)
    (hPQ : P ≤ normalizer (Q : Set G)) (hDP : D ≤ P)
    (hC : (C.subgroupOf Q).Normal) :
    let _ := hC
    ∀ action : P →* MulAut (Q ⧸ C.subgroupOf Q),
      (∀ actor : P, ∀ point : Q,
        action actor (QuotientGroup.mk' (C.subgroupOf Q) point) =
          QuotientGroup.mk' (C.subgroupOf Q)
            ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
              (mem_normalizer_iff.mp (hPQ actor.property) point).mp point.property⟩) →
      Nat.card (commutatorAction ((D.subgroupOf P).map action) (Q ⧸ C.subgroupOf Q)) =
        C.relIndex ⁅Q, D⁆ := by
  let _ := hC
  dsimp only
  intro action haction
  rw [quotient_conjugation_commutatorAction_eq_image P Q C D hPQ hDP hC action haction,
    ← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf
      (le_normalizer_iff_commutator_le_left.mp (hDP.trans hPQ))]

public theorem quotient_conjugation_quadratic_of_double_commutator_le
    {G : Type*} [Group G] (P Q C D : Subgroup G)
    (hPQ : P ≤ normalizer (Q : Set G)) (hDP : D ≤ P)
    (hC : (C.subgroupOf Q).Normal) (hdouble : ⁅⁅Q, D⁆, D⁆ ≤ C) :
    let _ := hC
    ∀ action : P →* MulAut (Q ⧸ C.subgroupOf Q),
      (∀ actor : P, ∀ point : Q,
        action actor (QuotientGroup.mk' (C.subgroupOf Q) point) =
          QuotientGroup.mk' (C.subgroupOf Q)
            ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
              (mem_normalizer_iff.mp (hPQ actor.property) point).mp point.property⟩) →
      commutatorAction₂ ((D.subgroupOf P).map action) (Q ⧸ C.subgroupOf Q) = ⊥ := by
  let _ := hC
  dsimp only
  intro action haction
  apply le_antisymm _ bot_le
  apply (closure_le (K := (⊥ : Subgroup (Q ⧸ C.subgroupOf Q)))).mpr
  rintro _ ⟨actor, point, hpoint, rfl⟩
  rw [quotient_conjugation_commutatorAction_eq_image P Q C D hPQ hDP hC action haction] at hpoint
  obtain ⟨lift, hlift, rfl⟩ := hpoint
  obtain ⟨representative, hrepresentative, heq⟩ := actor.property
  change (QuotientGroup.mk' (C.subgroupOf Q) lift)⁻¹ *
    (actor : MulAut (Q ⧸ C.subgroupOf Q)) (QuotientGroup.mk' (C.subgroupOf Q) lift) ∈ _
  rw [← heq, haction, ← map_inv, ← map_mul]
  apply mem_bot.mpr
  apply (QuotientGroup.eq_one_iff _).mpr
  change (lift : G)⁻¹ * ((representative : G) * (lift : G) * (representative : G)⁻¹) ∈ C
  simpa only [commutatorElement_def, inv_inv, mul_assoc, coe_subtype] using
    hdouble (commutator_mem_commutator (⁅Q, D⁆.inv_mem hlift) hrepresentative)

end Subgroup
