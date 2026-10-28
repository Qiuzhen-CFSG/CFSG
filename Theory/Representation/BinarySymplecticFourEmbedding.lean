module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod
public import Theory.SpecificGroups.PSp4Three.MatrixModel

/-!
# Coordinates for a faithful binary symplectic four-space

A symplectic basis turns a faithful representation preserving a nondegenerate
alternating form into an embedding in the concrete matrix group Sp₄(2).
The accompanying equation identifies its action with the original action.

This isolates the coordinate construction used in
`BinarySymplecticFourActorBound.lean`. The symplectic-basis theorem and its
ATLAS attribution are retained in the imported matrix-model module.
The source application is Aschbacher--Smith G.11.2(2), printed p.364.
-/

public noncomputable section
namespace Representation
open Matrix

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- A faithful action on a binary symplectic four-space embeds in Sp₄(2),
with the original action explicitly transported by a form isometry. -/
theorem exists_binarySymplecticFour_embedding
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4) (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ g v w, B (ρ g v) (ρ g w) = B v w) :
    ∃ (e : B.IsometryEquiv (PSp4Three.form (n := 2) (F := ZMod 2)))
      (j : G →* Matrix.symplecticGroup (Fin 2) (ZMod 2)),
      Function.Injective j ∧ ∀ g v, e (ρ g v) = (j g).val *ᵥ e v := by
  obtain ⟨e⟩ := PSp4Three.exists_isometry 2 B halt hn hd
  let σ : Representation (ZMod 2) G (PSp4Three.Vector 2 (ZMod 2)) :=
    e.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  let f := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp σ
  have hpres (g : G) : f g ∈ Matrix.symplecticGroup (Fin 2) (ZMod 2) := by
    apply PSp4Three.mem_iff_preserves.mpr
    intro v w
    change PSp4Three.form ((LinearMap.toMatrix' (σ g)) *ᵥ v)
      ((LinearMap.toMatrix' (σ g)) *ᵥ w) = _
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    change PSp4Three.form (e (ρ g (e.symm v))) (e (ρ g (e.symm w))) = _
    rw [e.map_app, hp]
    exact (e.map_app (e.symm w) (e.symm v)).symm.trans (by simp)
  let j : G →* Matrix.symplecticGroup (Fin 2) (ZMod 2) := f.codRestrict _ hpres
  refine ⟨e, j, ?_, ?_⟩
  · intro a b h
    apply hf
    apply e.toLinearEquiv.conjRingEquiv.injective
    apply LinearMap.toMatrixAlgEquiv'.injective
    exact congrArg Subtype.val h
  · intro g v
    change e (ρ g v) = (LinearMap.toMatrix' (σ g)) *ᵥ e v
    rw [LinearMap.toMatrix'_mulVec]
    change e (ρ g v) = e (ρ g (e.symm (e v)))
    exact (congrArg (fun w : V => e (ρ g w)) (e.toLinearEquiv.symm_apply_apply v)).symm

end Representation
