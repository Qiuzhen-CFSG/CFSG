module

public import Theory.SpecificGroups.PSp4Three.MatrixModel
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Mathlib.RepresentationTheory.Basic

/-!
# A marked faithful symplectic action in binary dimension four

A symplectic basis for the actual invariant alternating form transports the
specified representation into the standard matrix group. The transport retains
the action equation on every vector. Composing with the concrete six-letter
polar isomorphism gives a faithful permutation representation of degree six.
No group recognition follows merely from transitivity or the actor's order.

Source application: Aschbacher, Sporadic Groups, Lemma45.6 and Exercise15.1,
printed p.244. The existing symplectic-basis construction is imported unchanged.
-/

public section

namespace BinaryPolarity
open LinearMap Matrix
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

theorem exists_marked_symplectic_action_of_form
    (ρ : Representation (ZMod 2) A V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V=4)
    (B : LinearMap.BilinForm (ZMod 2) V) (hAlt : B.IsAlt) (hN : B.Nondegenerate)
    (hB : ∀ a x y, B (ρ a x) (ρ a y)=B x y) :
    ∃ e : B.IsometryEquiv (Matrix.PSp4Three.form (n:=2) (F:=ZMod 2)),
      ∃ φ : A →* Matrix.PSp4Three.Sp 2 (ZMod 2), Function.Injective φ ∧
        ∀ a x, (φ a).val *ᵥ (e x) = e (ρ a x) := by
  obtain ⟨e⟩ := Matrix.PSp4Three.exists_isometry 2 B hAlt hN hd
  let σ : Representation (ZMod 2) A (Matrix.PSp4Three.Vector 2 (ZMod 2)) :=
    e.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  let f := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp σ
  have hpres (a : A) : f a ∈ Matrix.symplecticGroup (Fin 2) (ZMod 2) := by
    apply Matrix.PSp4Three.mem_iff_preserves.mpr
    intro x y
    change Matrix.PSp4Three.form ((LinearMap.toMatrix' (σ a)) *ᵥ x)
      ((LinearMap.toMatrix' (σ a)) *ᵥ y)=_
    rw [LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]
    change Matrix.PSp4Three.form (e (ρ a (e.symm x))) (e (ρ a (e.symm y)))=_
    rw [e.map_app,hB]
    exact (e.map_app (e.symm y) (e.symm x)).symm.trans (by simp)
  let fSp : A →* Matrix.PSp4Three.Sp 2 (ZMod 2) := f.codRestrict _ hpres
  have hfinj : Function.Injective fSp := by
    intro a b he
    apply hf
    apply e.toLinearEquiv.conjRingEquiv.injective
    apply LinearMap.toMatrixAlgEquiv'.injective
    exact congrArg Subtype.val he
  refine ⟨e,fSp,hfinj,?_⟩
  intro a x
  change (LinearMap.toMatrix' (σ a)) *ᵥ (e x) = _
  rw [LinearMap.toMatrix'_mulVec]
  change e (ρ a (e.symm (e x))) = _
  exact congrArg (fun z => e (ρ a z)) (e.toLinearEquiv.symm_apply_apply x)

theorem exists_injective_six_action_of_form
    (ρ : Representation (ZMod 2) A V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V=4)
    (B : LinearMap.BilinForm (ZMod 2) V) (hAlt : B.IsAlt) (hN : B.Nondegenerate)
    (hB : ∀ a x y, B (ρ a x) (ρ a y)=B x y) :
    ∃ φ : A →* Equiv.Perm (Fin 6), Function.Injective φ := by
  obtain ⟨_,φ,hφ,_⟩ := exists_marked_symplectic_action_of_form ρ hf hd B hAlt hN hB
  exact ⟨Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp φ,
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective.comp hφ⟩
end BinaryPolarity
