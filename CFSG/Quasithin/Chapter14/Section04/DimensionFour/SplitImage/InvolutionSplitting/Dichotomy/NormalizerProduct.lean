module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.NormalizerProduct
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.MarkedCubic
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.PGroupCore

/-!
# The literal source quotient in the conditional normalizer lift

Apply the intrinsic lifting theorem with the actual Q = O₂(H),
K = O²(H), and π = QuotientGroup.mk' Q. The linear action used by the
marked dichotomy and the multiplicative central-quotient action have the
same kernel. A Sylow two-subgroup supplies H = KT by the residual Frattini
argument. The selected involution of Wᵍ produces exactly A = ⟨a,[U,a]⟩.

Three substantive inputs remain explicit: normalization of A by T,
centralizer control on the preimage of C_{K*}(a*), and the decomposition
K* = C_{K*}(a*) R*. The latter is a calculation in the actual action,
where R is the marked L₁. The first two need the genuine earlier block
arrangement; neither follows from the reduced local action hypotheses.
This conditional application does not complete 14.4.4. The normalizer-product
assembly owner must supply these inputs while retaining the original block,
its embeddings, and both dimension-four alternatives.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007; preceding markings in 12.8.2, 12.8.4–5 and 12.8.9–12.
-/

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting
variable {H : Type*} [Group H] [Finite H]

private theorem square_action_kernel (U : Subgroup H) [U.Normal]
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

/-- The marked involution gives the actual elementary sixteen and its literal
normalizer product, conditional on the remaining source controls. -/
public theorem marked_normalizer_product_of_controls
    (U : Subgroup H) [U.Normal] (d : QuaternionCentralProductData U)
    (hkernel : (d.normalSquareLinearAction U).ker = pCore 2 H)
    (hUK : U ≤ pResidual 2 H)
    (hK : IsElementaryAbelian 3 ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))))
    (R : Subgroup H) (hRn : (R.map (QuotientGroup.mk' (pCore 2 H))).Normal)
    (T : Sylow 2 H) (Wg : Subgroup H) (a : Wg)
    (ha : (a : H) ^ 2 = 1) (hout : (a : H) ∉ U)
    (hswap : d.left.map (MulAut.conjNormal (a : H)).toMonoidHom = d.right)
    (hT : (T : Subgroup H) ≤ normalizer
      ((zpowers (a : H) ⊔ ⁅U, zpowers (a : H)⁆ : Subgroup H) : Set H))
    (hKC : pResidual 2 H ⊓
      (centralizer ({QuotientGroup.mk' (pCore 2 H) (a : H)} : Set (H ⧸ pCore 2 H))).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ centralizer (centralizer (U : Set H) : Set H))
    (hcover : ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) ⊆
      (((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H)) ⊓
        centralizer ({QuotientGroup.mk' (pCore 2 H) (a : H)} : Set (H ⧸ pCore 2 H)) :
          Subgroup (H ⧸ pCore 2 H)) : Set (H ⧸ pCore 2 H)) *
            (R.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H))) :
    let A := zpowers (a : H) ⊔ ⁅U, zpowers (a : H)⁆
    IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      ((normalizer (A : Set H)).map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) *
        (R.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) = Set.univ := by
  have hs : (d.left.map U.subtype).map (MulAut.conj (a : H)).toMonoidHom =
      d.right.map U.subtype := by
    rw [map_map]
    have he : (MulAut.conj (a : H)).toMonoidHom.comp U.subtype =
        U.subtype.comp (MulAut.conjNormal (a : H)).toMonoidHom := rfl
    rw [he, ← map_map, hswap]
  obtain ⟨_, he, hc⟩ := d.elementary_sixteen_of_swap U a ha hout hs
  refine ⟨he, hc, ?_⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact d.normalizer_product_of_centralizer_control U (pCore 2 H) pCore_isPGroup
    ((square_action_kernel U d).trans hkernel) (pResidual 2 H) R T hUK a ha hKC hK
    hswap hT (pResidual_sup_sylow_eq_top T) hRn hcover

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting
