module
public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.GroupTheory.SubgroupConjugation
/-!
# Reconstructing a split extension from marked coordinates

A complement identifies the quotient with its actual actor subgroup.
Equivariant coordinates on the normal kernel and a marked quotient
isomorphism then reconstruct the group as their semidirect product.
The action is compared with original conjugation, not just its image.
-/
public section
namespace Subgroup
variable {G A W : Type*} [Group G] [Group A] [Group W]

lemma exists_semidirect_equiv_of_split_coordinates
    (Q K : Subgroup G) [Q.Normal] (hK : Q.IsComplement' K)
    (eA : (G ⧸ Q) ≃* A) (eQ : Q ≃* W) (ρ : A →* MulAut W)
    (he : ∀ (g : G) (u : Q), eQ (MulAut.conjNormal g u) =
      ρ (eA (QuotientGroup.mk' Q g)) (eQ u)) : Nonempty (G ≃* W ⋊[ρ] A) := by
  let eK := hK.symm.QuotientMulEquiv.symm.trans eA
  have heK (k : K) : eK k = eA (QuotientGroup.mk' Q k) := by
    apply congrArg eA
    change hK.symm.QuotientMulEquiv.symm k = QuotientGroup.mk' Q k
    apply hK.symm.QuotientMulEquiv.injective
    rw [MulEquiv.apply_symm_apply,quotientMulEquiv_mk_apply_of_isComplement']
  let γ : K →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion (Q.normalizer_eq_top ▸ le_top))
  have hc (k : K) : (γ k).trans eQ = eQ.trans (ρ (eK k)) := by
    apply MulEquiv.ext
    intro u
    change eQ (MulAut.conjNormal (k:G) u) = ρ (eK k) (eQ u)
    rw [he,heK]
  exact ⟨(SemidirectProduct.mulEquivSubgroup hK).symm.trans
    (SemidirectProduct.congr eQ eK hc)⟩
end Subgroup
