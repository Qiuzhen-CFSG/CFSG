module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.CyclicFour.Factors
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions
public import Theory.GroupTheory.QuaternionCentralProductQuotient

/-!
# Recognition of the order-64 Clifford group from its cyclic-four center

A finite group of order 64, with center ⟨z⟩ of order four and every square
in ⟨z²⟩, is multiplicatively equivalent to `EvenCliffordSix.Model`.
The Factors module constructs two commuting quaternion-eight subgroups.
Their diagonal quotient identifies their join with the model's quaternion
join; cyclic central-product gluing then adjoins the original center.

The intrinsic application uses the literal embedded volume in a subgroup
of the signed split extension. It retains the full-center equality as an
explicit hypothesis, to be discharged separately for the fixed-pair core.

Source: Aschbacher–Smith I.2.2(6a), printed pp.410 and 412, PDF pp.421 and
423 of the combined manuscript (1 March 2004). This module proves the
independent conditional recognition contract, not the missing center input.
-/

public section

open Subgroup
namespace EvenCliffordSix.CyclicFourRecognition
variable {G : Type*} [Group G] [Finite G]

private theorem nonempty_equiv (z : G) (horder : orderOf z = 4)
    (hcenter : center G = zpowers z) (hcard : Nat.card G = 64)
    (hsq : ∀ x : G, x ^ 2 ∈ zpowers (z ^ 2)) : Nonempty (G ≃* Model) := by
  obtain ⟨Q, R, hQ, hR, hinter, hcomm, hgen⟩ :=
    exists_factors z horder hcenter hcard hsq
  let B : Subgroup G := Q ⊔ R
  have hsignCard : Nat.card (zpowers (z ^ 2)) = 2 := by
    rw [Nat.card_zpowers, orderOf_pow, horder]
    decide
  let d : QuaternionCentralProductData B := {
    left := Q.subgroupOf B
    right := R.subgroupOf B
    left_model := ⟨(subgroupOfEquivOfLe (show Q ≤ B from le_sup_left)).trans hQ.some⟩
    right_model := ⟨(subgroupOfEquivOfLe (show R ≤ B from le_sup_right)).trans hR.some⟩
    intersection_card := by
      change Nat.card ((Q ⊓ R).subgroupOf B) = 2
      rw [Nat.card_congr (subgroupOfEquivOfLe
        (show Q ⊓ R ≤ B from inf_le_left.trans le_sup_left)).toEquiv, hinter]
      exact hsignCard
    commute := fun q hq r hr => Subtype.ext (hcomm q hq r hr)
    span := by
      rw [← subgroupOf_sup (show Q ≤ B from le_sup_left) (show R ≤ B from le_sup_right)]
      exact subgroupOf_self B }
  have hZ : zpowers z ≤ center G := le_of_eq hcenter.symm
  have hupper : zpowers z ⊓ B ≤ (center B).map B.subtype := by
    intro x hx
    exact ⟨⟨x, hx.2⟩, mem_center_iff.mpr
      (fun b => Subtype.ext (mem_center_iff.mp (hZ hx.1) b)), rfl⟩
  have hlower : zpowers (z ^ 2) ≤ zpowers z ⊓ B := by
    refine le_inf (zpowers_le.mpr ((zpowers z).pow_mem (mem_zpowers z) 2)) ?_
    rw [← hinter]
    exact inf_le_left.trans le_sup_left
  have hover : Nat.card (zpowers z ⊓ B : Subgroup G) = 2 := by
    have hu := Subgroup.card_le_of_le hupper
    have hl := Subgroup.card_le_of_le hlower
    rw [card_subtype, d.center_card] at hu
    rw [hsignCard] at hl
    omega
  let eZ : Structure.cyclicFactor ≃* zpowers z := mulEquivOfCyclicCardEq (by
    rw [Structure.cyclicFactor_card, Nat.card_zpowers, horder])
  let eB : Structure.quaternionJoin ≃* B :=
    Structure.quaternionData.nonempty_model_equiv.some.trans d.nonempty_model_equiv.some.symm
  obtain ⟨e, _, _⟩ := Structure.exists_equiv_of_cyclic_central_product
    (zpowers z) B hZ hgen hover eZ eB
  exact ⟨e.symm⟩

/-- Recognition from order 64, the exact cyclic-four center, and binary squares.
The factors and the multiplicative equivalence are constructed from these inputs. -/
noncomputable def equivOfCyclicFourCenter (z : G) (horder : orderOf z = 4)
    (hcenter : center G = zpowers z) (hcard : Nat.card G = 64)
    (hsq : ∀ x : G, x ^ 2 ∈ zpowers (z ^ 2)) : G ≃* Model :=
  (nonempty_equiv z horder hcenter hcard hsq).some

end EvenCliffordSix.CyclicFourRecognition

namespace EvenCliffordSix.SplitExtension.ElementaryRestrictions

/-- The intrinsic elementary restriction is the Clifford group once its full
center is the distinguished embedded C₄. -/
noncomputable def equivOfCenter (H : Subgroup SplitExtension) (hZ : central ≤ H)
    (hcard : Nat.card H = 64) (hsq : ∀ x ∈ H, x ^ 2 ∈ sign)
    (hcenter : center H = centralIn H) : H ≃* Model :=
  CyclicFourRecognition.equivOfCyclicFourCenter (volumeIn H hZ) (volumeIn_order H hZ)
    (hcenter.trans (centralIn_eq_zpowers_volume H hZ)) hcard
    (square_mem_volume_sq H hsq hZ)

end EvenCliffordSix.SplitExtension.ElementaryRestrictions
