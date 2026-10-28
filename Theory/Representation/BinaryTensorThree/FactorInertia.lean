module
public import Theory.Representation.BinaryTensorThree.Normalizer

/-!
# Inner automorphisms on a preserved binary tensor factor

An invertible intertwiner of one natural factor of the binary three-by-three
tensor has two invertible tensor factors. Faithfulness of the base action
then identifies its automorphism of that factor as inner. Transport through
an arbitrary equivariant marking gives the same conclusion for every element
of the original component normalizer; the ambient action need not be faithful.

This eliminates the invariant tensor alternative in Aschbacher--Smith
F.9.18(5ii) when the component normalizer induces a diagram automorphism,
as in14.6.22, printed pp.325--326,1038.
-/

public noncomputable section
open Subgroup Representation
namespace BinaryTensorThree

/-- The action of the second natural factor on the literal tensor space. -/
@[expose] def rightRepresentation : Representation (ZMod 2) Factor Space :=
  action.comp (baseEmbedding.comp (MonoidHom.inr _ _))

/-- Every automorphism implemented on a preserved tensor factor is inner. -/
theorem inner_of_right_tensor_intertwining
    (f : Space ≃ₗ[ZMod 2] Space) (φ : Factor → Factor)
    (hf : ∀ g X, f (baseAction (1,g) X) = baseAction (1,φ g) (f X)) :
    ∃ b : Factor, ∀ g, φ g = b*g*b⁻¹ := by
  obtain ⟨a,b,rfl⟩ := tensor_factors_of_right_intertwining f φ hf
  refine ⟨b,fun g => ?_⟩
  have he : baseAction (a,b) * baseAction (1,g) =
      baseAction (1,φ g) * baseAction (a,b) := LinearEquiv.ext (hf g)
  rw [←map_mul,←map_mul] at he
  have hh := congrArg Prod.snd (baseAction_injective he)
  change b*g = φ g*b at hh
  exact (eq_mul_inv_iff_mul_eq.mpr hh.symm)

variable {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- A tensor-factor marking forces inner action by the whole original normalizer. -/
theorem normalizer_inner_of_right_tensor
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D)
    (e : K ≃* Factor)
    (b : Representation.Equiv (ρ.comp K.subtype) (rightRepresentation.comp e.toMonoidHom))
    (s : normalizer (K : Set D)) :
    ∃ k : K, K.normalizerMonoidHom s = MulAut.conj k := by
  let α := K.normalizerMonoidHom s
  let φ : Factor → Factor := fun g => e (α (e.symm g))
  let L := b.toLinearEquiv
  let f : Space ≃ₗ[ZMod 2] Space := L.symm.trans
    ((LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom s.val)).trans L)
  have hb (k : K) (v : V) : L (ρ k.val v) = baseAction (1,e k) (L v) :=
    Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap k v
  have hf (g : Factor) (X : Space) :
      f (baseAction (1,g) X) = baseAction (1,φ g) (f X) := by
    obtain ⟨k,rfl⟩ := e.surjective g
    obtain ⟨v,rfl⟩ := L.surjective X
    rw [←hb]
    change L (ρ s.val (L.symm (L (ρ k.val v)))) =
      baseAction (1,φ (e k)) (L (ρ s.val (L.symm (L v))))
    rw [L.symm_apply_apply,L.symm_apply_apply]
    have hφ : φ (e k) = e (α k) := by simp only [φ,e.symm_apply_apply]
    rw [hφ,←hb]
    congr 1
    change ρ s.val (ρ k.val v) = ρ (s.val*k.val*s.val⁻¹) (ρ s.val v)
    simp only [map_mul,Module.End.mul_apply,ρ.inv_self_apply]
  obtain ⟨c,hc⟩ := inner_of_right_tensor_intertwining f φ hf
  refine ⟨e.symm c,?_⟩
  apply MulEquiv.ext
  intro k
  apply e.injective
  have hh := hc (e k)
  simpa only [φ,e.symm_apply_apply,MulAut.conj_apply,map_mul,map_inv,e.apply_symm_apply]
    using hh

end BinaryTensorThree
