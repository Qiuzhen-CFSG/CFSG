module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeQuotientOrbit
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairTransport
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson.Centralizers

/-!
# Exact local class size for the native row-seven pair

The quotient orbit certificate supplies the lower bound 1155 and the row-seven
forest supplies the lower bound 96 for the two factors in the local class
count. The reverse counting map is injective, so the existing upper bound is
sharp. This fixes the centralizer order without using a printed MOG
centralizer table.
-/

public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
open Subgroup Theory.GroupTheory
open Janko4.Cardinality
open Janko4.Cardinality.LocalInvolutionCensus
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.FiberCensus
open Cardinality.LocalInvolutionCensus.Coordinates
open LowerBound
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
attribute [local irreducible] modelGroup matrixA matrixB

private theorem mask_injective : Function.Injective (fun i : Fin 96 => Forest.maskAt 7 i.val) := by
  decide +kernel

theorem fiber_seven_lower : 96 ≤ Nat.card (classFiber (representative 7)) := by
  let f : Fin 96 → classFiber (representative 7) := fun i =>
    ⟨element 3 (Forest.maskAt 7 i.val), by
      constructor
      · have h := sourceSubgroupEquivLocal.toMonoidHom.map_isConj
          (Forest.node_isConj_of_edges (Forest.edges Cardinality.Thompson.max2_card.le)
            7 i.val i.isLt)
        simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
          sourceEquiv_representative, sourceEquiv_element,
          show fiberIndex 7 = 3 from rfl] using h
      · change q (localKernelProduct _ * lift 3) = q (representative 7)
        rw [map_mul, q_localKernelProduct, one_mul, q_representative]
        rfl⟩
  have hi : Function.Injective f := by
    intro i j he
    have hx := congrArg Subtype.val he
    change localKernelProduct (Forest.maskAt 7 i.val) * lift 3 =
      localKernelProduct (Forest.maskAt 7 j.val) * lift 3 at hx
    exact mask_injective (kernelProduct_injective
      (sourceSubgroupEquivLocal.injective (mul_right_cancel hx)))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hi

theorem localClass_card_ge_quotient_mul_fiber (r : H) :
    Nat.card (quotientClass (q r)) * Nat.card (classFiber r) ≤
      Nat.card (localClass r) := by
  classical
  have hchoose (v : quotientClass (q r)) :
      ∃ g : H, q g * q r * (q g)⁻¹ = v.val := by
    obtain ⟨c, hc⟩ := isConj_iff.mp v.property
    obtain ⟨g, rfl⟩ := q_surjective c
    exact ⟨g, hc⟩
  choose g hg using hchoose
  let f : quotientClass (q r) × classFiber r → localClass r := fun p =>
    ⟨g p.1 * p.2.val * (g p.1)⁻¹,
      p.2.property.1.trans (isConj_iff.mpr ⟨g p.1, rfl⟩)⟩
  have hq (v : quotientClass (q r)) (u : classFiber r) : q (f (v, u)).val = v.val := by
    change q (g v * u.val * (g v)⁻¹) = v.val
    rw [map_mul, map_mul, map_inv, u.property.2, hg]
  have hi : Function.Injective f := by
    rintro ⟨v,u⟩ ⟨w,t⟩ he
    have hvw : v = w := by
      apply Subtype.ext
      rw [← hq v u, ← hq w t]
      exact congrArg (fun a : localClass r => q a.val) he
    subst w
    have hut : u = t := by
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      change g v * u.val * (g v)⁻¹ = g v * t.val * (g v)⁻¹ at he'
      exact mul_left_cancel (mul_right_cancel he')
    exact Prod.ext rfl hut
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hi

theorem localClass_seven_card : Nat.card (localClass (representative 7)) = 110880 := by
  have hlo := localClass_card_ge_quotient_mul_fiber (representative 7)
  have hq := NativeQuotientOrbit.quotient_class_lower
  have hf := fiber_seven_lower
  have hge : 110880 ≤ Nat.card (localClass (representative 7)) := by
    have hh : 1155 * 96 ≤
        Nat.card (quotientClass (q (lift 3))) *
          Nat.card (classFiber (representative 7)) := Nat.mul_le_mul hq hf
    have hnum : 1155 * 96 = 110880 := by norm_num
    rw [hnum] at hh
    apply hh.trans
    simpa only [q_representative, show fiberIndex 7 = 3 from rfl] using hlo
  have hle : Nat.card (localClass (representative 7)) ≤
      quotientBound (fiberIndex 7) * fiberBound 7 :=
    representative_class_card_le Cardinality.Thompson.max2_card.le 7
      (by simp [FiberCensus.Required])
  norm_num [quotientBound, fiberBound] at hle
  exact Nat.le_antisymm hle hge

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
