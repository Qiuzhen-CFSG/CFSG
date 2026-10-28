module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy
public import Theory.GroupTheory.PResidual.Defs
public import Theory.PGroupCore

/-!
# The marked quaternion action alternative in dimension four

Apply the intrinsic dichotomy to the literal normalizer action on the embedded
normal U, with Q = O₂(H) and K = O²(H). The marked cubic R = L₁ supplies the
full commutator space and the inversion hypothesis. In the c₂ branch the
proof derives both outer factor restrictions and inversion of every element
of K*. In the swapping branch it constructs precisely A = ⟨a,[U,a]⟩.

Only the chosen element of Wᵍ is assumed involutory. The source defines
W = C_U(V₂); it does not supply elementary structure of the whole Wᵍ.
This application does not assert the further normalizer product or nonsplitting
of L over V. Those require the remaining source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 14.4.4, printed p.1007; Notation 12.8 and Lemma 12.8.9, pp.852–853.
-/

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting
variable {H : Type*} [Group H] [Finite H]

/-- Apply the proved action alternative to the actual two-core quotient and
two-residual, keeping the selected involution in its marked subgroup. -/
public theorem marked_normalizer_action_dichotomy
    (U : Subgroup H) [U.Normal] (d : QuaternionCentralProductData U)
    (hkernel : (d.normalSquareLinearAction U).ker = pCore 2 H)
    (hK : IsElementaryAbelian 3 ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))))
    (R : Subgroup H) (hR : Nat.card (R.map (QuotientGroup.mk' (pCore 2 H))) = 3)
    (hmove : subspaceCommutator (d.normalSquareRepresentation U) ⊤ R = ⊤)
    (Wg : Subgroup H) (a : Wg) (ha : (a : H)^2=1) (hout : (a : H) ∉ U)
    (hinv : ∀ r ∈ R, QuotientGroup.mk' (pCore 2 H) ((a : H)*r*(a : H)⁻¹) =
      (QuotientGroup.mk' (pCore 2 H) r)⁻¹) :
    let α := U.normalizerMonoidHom
      ⟨(a : H), by rw [U.normalizer_eq_top]; exact mem_top _⟩
    (d.IsC2Action α ∧ d.BothOuter α ∧
      ∀ k ∈ pResidual 2 H, QuotientGroup.mk' (pCore 2 H) ((a : H)*k*(a : H)⁻¹) =
        (QuotientGroup.mk' (pCore 2 H) k)⁻¹) ∨
      (d.IsA2Action α ∧
        (d.left.map U.subtype).map (MulAut.conj (a : H)).toMonoidHom = d.right.map U.subtype ∧
        ⁅U,zpowers (a : H)⁆ = U ⊓ centralizer ({(a : H)} : Set H) ∧
        IsElementaryAbelian 2 (zpowers (a : H) ⊔ ⁅U,zpowers (a : H)⁆ : Subgroup H) ∧
        Nat.card (zpowers (a : H) ⊔ ⁅U,zpowers (a : H)⁆ : Subgroup H) = 16) := by
  have he : U.normalizerMonoidHom
      ⟨(a : H), by rw [U.normalizer_eq_top]; exact mem_top _⟩ = MulAut.conjNormal (a : H) := by
    ext u
    rfl
  dsimp only
  rw [he]
  exact d.marked_action_dichotomy_with_cubic_inversion U (pCore 2 H) hkernel
    (pResidual 2 H) hK R hR hmove a ha hout hinv

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting
