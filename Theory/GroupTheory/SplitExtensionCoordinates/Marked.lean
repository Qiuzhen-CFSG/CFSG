module
public import Theory.GroupTheory.SplitExtensionCoordinates

/-!
# Kernel-marked coordinates for a split extension

The standard complement equivalence and equivariant coordinates reconstruct
an actual semidirect product. This refinement records the value on every
kernel element, and consequently identifies the image of the original
normal subgroup with the canonical left factor.

The consumer is the literal natural A₆ split block in Aschbacher–Smith 14.3.19(9).
-/

public noncomputable section
namespace Subgroup
variable {G A W : Type*} [Group G] [Group A] [Group W]

theorem exists_marked_semidirect_equiv_of_split_coordinates
    (Q K : Subgroup G) [Q.Normal] (hK : Q.IsComplement' K)
    (eA : (G ⧸ Q) ≃* A) (eQ : Q ≃* W) (ρ : A →* MulAut W)
    (he : ∀ (g : G) (u : Q), eQ (MulAut.conjNormal g u) =
      ρ (eA (QuotientGroup.mk' Q g)) (eQ u)) :
    ∃ e : G ≃* W ⋊[ρ] A,
      (∀ u : Q, e u = SemidirectProduct.inl (eQ u)) ∧
      Q.map e.toMonoidHom = (SemidirectProduct.inl : W →* W ⋊[ρ] A).range := by
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
  let m := SemidirectProduct.mulEquivSubgroup hK
  let e : G ≃* W ⋊[ρ] A := m.symm.trans (SemidirectProduct.congr eQ eK hc)
  have heu (u : Q) : e u=SemidirectProduct.inl (eQ u) := by
    have hm : m.symm u=SemidirectProduct.inl u := by
      apply m.injective
      rw [m.apply_symm_apply]
      simp [m]
    change SemidirectProduct.congr eQ eK hc (m.symm u)=_
    rw [hm]
    apply SemidirectProduct.ext <;> simp
  refine ⟨e,heu,le_antisymm ?_ ?_⟩
  · rintro _ ⟨u,hu,rfl⟩
    exact ⟨eQ ⟨u,hu⟩,(heu ⟨u,hu⟩).symm⟩
  · rintro _ ⟨w,rfl⟩
    refine ⟨eQ.symm w,(eQ.symm w).property,?_⟩
    exact (heu (eQ.symm w)).trans (congrArg SemidirectProduct.inl (eQ.apply_symm_apply w))
end Subgroup
