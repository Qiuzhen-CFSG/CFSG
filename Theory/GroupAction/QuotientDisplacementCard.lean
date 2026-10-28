module
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# Exact cardinality of quotient conjugation displacement

For a supplied conjugation action of P on V/Z and an actor subgroup D≤P,
the image-action commutator has order n exactly when [V,D] joined with Z
has order n times |Z|. The same quotient normality instance and action
formula are retained, and Z need only be normal inside V.

The existing image-cardinality theorem gives the relative index of Z in
[V,D]. Normality in V identifies that index with the index in the join.
The subgroup index/card formula then gives the equivalence, including n=0.

This source-neutral bridge converts the quotient-displacement conditions
in Stellmacher (9.4) and (10.1) into cardinalities in a literal action.
-/

namespace Subgroup

public theorem quotient_conjugation_commutatorAction_card_iff
    {G : Type*} [Group G] [Finite G] (P V Z D : Subgroup G)
    (hPV : P ≤ normalizer (V : Set G)) (hDP : D ≤ P) (hZV : Z ≤ V)
    [hN : (Z.subgroupOf V).Normal]
    (action : P →* MulAut (V ⧸ Z.subgroupOf V))
    (hformula : ∀ actor : P, ∀ point : V,
      action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
        QuotientGroup.mk' (Z.subgroupOf V)
          ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
            (mem_normalizer_iff.mp (hPV actor.property) point).mp point.property⟩)
    (n : ℕ) :
    Nat.card (commutatorAction ((D.subgroupOf P).map action) (V ⧸ Z.subgroupOf V)) = n ↔
      Nat.card (⁅V, D⁆ ⊔ Z : Subgroup G) = n * Nat.card Z := by
  let C := ⁅V, D⁆
  have hCV : C ≤ V := le_normalizer_iff_commutator_le_left.mp (hDP.trans hPV)
  have hjoinV : C ⊔ Z ≤ V := sup_le hCV hZV
  have hindex := relIndex_sup_right (C.subgroupOf V) (Z.subgroupOf V)
  rw [← subgroupOf_sup hCV hZV, relIndex_subgroupOf hjoinV,
    relIndex_subgroupOf hCV] at hindex
  have hcount := (Z.subgroupOf (C ⊔ Z)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show Z ≤ C ⊔ Z from le_sup_right)).toEquiv] at hcount
  change Z.relIndex (C ⊔ Z) * Nat.card Z = Nat.card (C ⊔ Z : Subgroup G) at hcount
  rw [hindex] at hcount
  rw [quotient_conjugation_commutatorAction_card P V Z D hPV hDP hN action hformula]
  constructor
  · intro hh
    exact hcount.symm.trans (congrArg (fun k : ℕ => k * Nat.card Z) hh)
  · intro hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcount.trans hh)

end Subgroup
