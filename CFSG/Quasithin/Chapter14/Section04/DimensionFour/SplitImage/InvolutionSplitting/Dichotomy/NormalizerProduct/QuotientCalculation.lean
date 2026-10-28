module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.NormalizerProduct.QuotientCalculation
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.MarkedCubic
public import Theory.PGroupCore

/-!
# The cubic product for the marked dimension-four quotient

Use Q = O₂(H), K = O²(H), and the literal quotient map. The action kernel is
specified using the same binary representation as the marked action dichotomy.
The factor-interchange hypothesis retains the embedded quaternion factors in H,
exactly as in the conclusion of marked_normalizer_action_dichotomy.

The intrinsic calculation proves K* = C_{K*}(a*) R*. Thus it discharges the
quotient coverage input in marked_normalizer_product_of_controls for both
source alternatives. No model identification or additional lifting premise is
needed for this calculation. The normalization and centralizer-control inputs
of that conditional normalizer theorem remain separate source obligations.
The full commutator-space marking and a ∉ U are unnecessary for this step.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 14.4.4, printed p.1007, with R the actual marked L₁.
-/

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting
variable {H : Type*} [Group H] [Finite H]

private theorem quotient_calculation_square_kernel (U : Subgroup H) [U.Normal]
    (d : QuaternionCentralProductData U) :
    ((quotientAut (center U)).comp (MulAut.conjNormal : H →* MulAut U)).ker =
      (d.normalSquareLinearAction U).ker := by
  ext h
  change quotientAut (center U) (MulAut.conjNormal h) = 1 ↔
    d.normalSquareLinearAction U h = 1
  constructor
  · intro he
    apply LinearEquiv.ext
    intro v
    change d.quotientLinearAction (MulAut.conjNormal h) (Additive.ofMul v.toMul) = v
    rw [d.quotientLinearAction_apply, he]
    rfl
  · intro he
    apply MulEquiv.ext
    intro v
    have hh := DFunLike.congr_fun he (Additive.ofMul v)
    change d.quotientLinearAction (MulAut.conjNormal h) (Additive.ofMul v) = Additive.ofMul v at hh
    rw [d.quotientLinearAction_apply] at hh
    exact congrArg Additive.toMul hh

/-- The swapping branch gives the exact quotient coverage required by the
normalizer-product lift, retaining the marked involution and embedded factors. -/
public theorem marked_quotient_cubic_product
    (U : Subgroup H) [U.Normal] (d : QuaternionCentralProductData U)
    (hkernel : (d.normalSquareLinearAction U).ker = pCore 2 H)
    (hK : IsElementaryAbelian 3 ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))))
    (hKcard : Nat.card ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))) = 9)
    (R : Subgroup H) (hRn : (R.map (QuotientGroup.mk' (pCore 2 H))).Normal)
    (hRcard : Nat.card (R.map (QuotientGroup.mk' (pCore 2 H))) = 3)
    (Wg : Subgroup H) (a : Wg) (ha : (a : H)^2=1)
    (hswap : (d.left.map U.subtype).map (MulAut.conj (a : H)).toMonoidHom =
      d.right.map U.subtype)
    (hinv : ∀ r ∈ R, QuotientGroup.mk' (pCore 2 H) ((a : H)*r*(a : H)⁻¹) =
      (QuotientGroup.mk' (pCore 2 H) r)⁻¹) :
    ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) =
      (((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H)) ⊓
        centralizer {QuotientGroup.mk' (pCore 2 H) (a : H)} : Subgroup (H ⧸ pCore 2 H)) :
          Set (H ⧸ pCore 2 H)) * (R.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) := by
  have hs : d.left.map (MulAut.conjNormal (a : H)).toMonoidHom = d.right := by
    apply map_injective U.subtype_injective
    rw [map_map]
    have he : U.subtype.comp (MulAut.conjNormal (a : H)).toMonoidHom =
        (MulAut.conj (a : H)).toMonoidHom.comp U.subtype := rfl
    rw [he, ← map_map]
    exact hswap
  exact d.residual_quotient_cubic_product U (pCore 2 H)
    ((quotient_calculation_square_kernel U d).trans hkernel) hK hKcard R hRn hRcard a ha hs hinv

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting
