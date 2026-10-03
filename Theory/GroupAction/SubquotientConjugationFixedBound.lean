module

public import Theory.GroupAction.QuotientConjugationFixedBound

/-!
# Common fixed-index bounds on actual subgroup quotients

A centralizer-index bound descends first to a subgroup and then to an
actual quotient with its specified conjugation action. The fixed subgroup
belongs to the entire actor image, not merely a cyclic subgroup generated
by one actor. No elementary abelian or coprimality hypothesis is needed.
-/

namespace Subgroup

public theorem subgroup_centralizer_card_bound
    {G : Type*} [Group G] [Finite G] (C E A : Subgroup G)
    (hEC : E ≤ C) (bound : ℕ)
    (hbound : Nat.card C ≤ bound * Nat.card (C ⊓ centralizer (A : Set G) : Subgroup G)) :
    Nat.card E ≤ bound * Nat.card (E ⊓ centralizer (A : Set G) : Subgroup G) := by
  let F := centralizer (A : Set G)
  have hcard (U : Subgroup G) :
      Nat.card (F.subgroupOf U) = Nat.card (U ⊓ F : Subgroup G) := by
    rw [← inf_subgroupOf_left F U]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hidx : F.relIndex C ≤ bound := by
    change (F.subgroupOf C).index ≤ bound
    change Nat.card C ≤ bound * Nat.card (C ⊓ F : Subgroup G) at hbound
    rw [← hcard C, ← (F.subgroupOf C).card_mul_index, mul_comm bound] at hbound
    exact Nat.le_of_mul_le_mul_left hbound Nat.card_pos
  have hidxE : (F.subgroupOf E).index ≤ bound :=
    (relIndex_le_of_le_right hEC (FiniteIndex.index_ne_zero (H := F.subgroupOf C))).trans
      hidx
  change Nat.card E ≤ bound * Nat.card (E ⊓ F : Subgroup G)
  rw [← hcard E, ← (F.subgroupOf E).card_mul_index, mul_comm bound]
  exact Nat.mul_le_mul_left _ hidxE

public theorem quotient_conjugation_actor_fixed_card_bound
    {G : Type*} [Group G] [Finite G] (P U Z A : Subgroup G)
    (hPU : P ≤ normalizer (U : Set G)) (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    ∀ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ actor : P, ∀ value : U,
        action actor (QuotientGroup.mk' (Z.subgroupOf U) value) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(actor : G) * (value : G) * (actor : G)⁻¹,
              (mem_normalizer_iff.mp (hPU actor.property) value).mp value.property⟩) →
      ∀ bound : ℕ,
      Nat.card U ≤ bound * Nat.card (U ⊓ centralizer (A : Set G) : Subgroup G) →
      Nat.card (U ⧸ Z.subgroupOf U) ≤ bound *
        Nat.card (FixedPoints.subgroup ((A.subgroupOf P).map action)
          (U ⧸ Z.subgroupOf U)) := by
  let _ := hN
  dsimp only
  intro action haction bound hbound
  let quotientMap := QuotientGroup.mk' (Z.subgroupOf U)
  let central := U ⊓ centralizer (A : Set G)
  let restricted := central.subgroupOf U
  let fixed := FixedPoints.subgroup ((A.subgroupOf P).map action) (U ⧸ Z.subgroupOf U)
  have hcard : Nat.card restricted = Nat.card central :=
    Nat.card_congr (subgroupOfEquivOfLe (show central ≤ U from inf_le_left)).toEquiv
  have hmap : restricted.map quotientMap ≤ fixed := by
    rintro value ⟨preimage, hpreimage, rfl⟩ actor
    obtain ⟨actorP, hactorA, hactor⟩ := actor.property
    have hcomm : (actorP : G) * (preimage : G) = (preimage : G) * (actorP : G) :=
      mem_centralizer_iff.mp hpreimage.2 actorP hactorA
    change (actor : MulAut (U ⧸ Z.subgroupOf U)) (quotientMap preimage) = _
    rw [← hactor, haction]
    apply congrArg quotientMap
    apply Subtype.ext
    change (actorP : G) * (preimage : G) * (actorP : G)⁻¹ = (preimage : G)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hidx : restricted.index ≤ bound := by
    rw [← hcard, ← restricted.card_mul_index, mul_comm bound] at hbound
    exact Nat.le_of_mul_le_mul_left hbound Nat.card_pos
  have hfixed : fixed.index ≤ restricted.index :=
    (index_antitone hmap).trans (Nat.le_of_dvd
      (Nat.pos_of_ne_zero (FiniteIndex.index_ne_zero (H := restricted)))
      (restricted.index_map_dvd (QuotientGroup.mk'_surjective (Z.subgroupOf U))))
  rw [← fixed.card_mul_index, mul_comm bound]
  exact Nat.mul_le_mul_left _ (hfixed.trans hidx)

public theorem subquotient_conjugation_actor_fixed_card_bound
    {G : Type*} [Group G] [Finite G] (P C E D A : Subgroup G)
    (hEC : E ≤ C) (hPE : P ≤ normalizer (E : Set G))
    (hN : (D.subgroupOf E).Normal) :
    let _ := hN
    ∀ action : P →* MulAut (E ⧸ D.subgroupOf E),
      (∀ actor : P, ∀ value : E,
        action actor (QuotientGroup.mk' (D.subgroupOf E) value) =
          QuotientGroup.mk' (D.subgroupOf E)
            ⟨(actor : G) * (value : G) * (actor : G)⁻¹,
              (mem_normalizer_iff.mp (hPE actor.property) value).mp value.property⟩) →
      ∀ bound : ℕ,
      Nat.card C ≤ bound * Nat.card (C ⊓ centralizer (A : Set G) : Subgroup G) →
      Nat.card (E ⧸ D.subgroupOf E) ≤ bound *
        Nat.card (FixedPoints.subgroup ((A.subgroupOf P).map action)
          (E ⧸ D.subgroupOf E)) := by
  let _ := hN
  dsimp only
  intro action haction bound hbound
  exact quotient_conjugation_actor_fixed_card_bound P E D A hPE hN action haction bound
    (subgroup_centralizer_card_bound C E A hEC bound hbound)

end Subgroup

