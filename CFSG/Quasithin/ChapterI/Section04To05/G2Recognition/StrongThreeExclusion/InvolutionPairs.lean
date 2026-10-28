module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.SpecialSupport
public import Theory.Character.InvolutionRootPairing

/-!
# Localization of involution factorizations in the Sylow-nine branch

An involution factor in a product inverts that product. If the product lies
in H and has order divisible by three, the three-singular transporter theorem
puts both factors in H. Thus the actual ambient and local pair counts agree
on the support used for character induction, and Frobenius reciprocity
preserves the corresponding pairing.
-/

public section
noncomputable section
attribute [local instance] Fintype.ofFinite
open Subgroup Theory.GroupTheory Theory.Character
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

private theorem involution_pair_mem_H
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) (a : c.H) (ha : 3 ∣ orderOf a)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : x * y = (a : G)) : x ∈ c.H ∧ y ∈ c.H := by
  have hx2 : x * x = 1 := by simpa only [hx, pow_two] using pow_orderOf_eq_one x
  have hy2 : y * y = 1 := by simpa only [hy, pow_two] using pow_orderOf_eq_one y
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2
  have hxH : x ∈ c.H := by
    apply three_singular_transporter_mem_H c hsmall a a⁻¹ ha x
    change x⁻¹ * (a : G) * x = (a : G)⁻¹
    rw [← hxy, mul_inv_rev, hxi, hyi]
    simp only [← mul_assoc, hx2, one_mul]
  refine ⟨hxH, ?_⟩
  have hyH := c.H.mul_mem (c.H.inv_mem hxH) a.property
  simpa only [← hxy, inv_mul_cancel_left] using hyH

/-- Every involution factorization of a three-singular element of H is
already a factorization inside H. -/
theorem three_singular_involutionPairCount
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) (a : c.H) (ha : 3 ∣ orderOf a) :
    involutionPairCount (a : G) = involutionPairCount a := by
  unfold involutionPairCount
  apply Nat.card_congr
  exact {
    toFun := fun p => by
      have hm := involution_pair_mem_H c hsmall a ha p.val.1 p.val.2
        p.property.1 p.property.2.1 p.property.2.2
      exact ⟨(⟨p.val.1, hm.1⟩, ⟨p.val.2, hm.2⟩),
        (orderOf_coe _).symm.trans p.property.1,
        (orderOf_coe _).symm.trans p.property.2.1,
        Subtype.ext p.property.2.2⟩
    invFun := fun p => ⟨(p.val.1.val, p.val.2.val),
      (orderOf_coe _).trans p.property.1,
      (orderOf_coe _).trans p.property.2.1,
      congrArg Subtype.val p.property.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Induction preserves the pairing with the literal involution-product
count for every function supported on the three-singular elements of H. -/
theorem three_singular_induction_involutionPairCount
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G)
    (φ : ClassFunction c.H) (hφ : supportedOn φ {a : c.H | 3 ∣ orderOf a}) :
    scalarProduct G (inducedClassFunction c.H φ)
      (fun a => (involutionPairCount a : ℂ)) =
    scalarProduct c.H φ (fun a => (involutionPairCount a : ℂ)) := by
  classical
  rw [scalarProduct_inducedClassFunction _ _ involutionPairCount_isClassFunction]
  unfold scalarProduct
  rw [Subsingleton.elim (Fintype.ofFinite c.H) (inferInstance : Fintype c.H)]
  congr 1
  apply Fintype.sum_congr
  intro a
  dsimp only
  by_cases ha : 3 ∣ orderOf a
  · rw [three_singular_involutionPairCount c hsmall a ha]
  · rw [hφ a ha, zero_mul, zero_mul]

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
