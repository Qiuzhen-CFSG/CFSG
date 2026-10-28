module

public import Theory.SpecificGroups.PSp4Three.MatrixModel
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Marked symplectic actions in arbitrary even dimension

A symplectic basis transports a faithful binary representation preserving
an alternating nondegenerate form into the actual standard matrix group.
The result retains the equation on every original vector. This supplies the
matrix carrier used in the C₃ recognition of Aschbacher–Smith I.5.15, p.424.
-/

public section
namespace BinaryPolarity
open LinearMap Matrix
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

theorem exists_marked_symplectic_action
    (n : ℕ) (ρ : Representation (ZMod 2) A V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 2 * n)
    (B : LinearMap.BilinForm (ZMod 2) V) (hAlt : B.IsAlt) (hN : B.Nondegenerate)
    (hB : ∀ a x y, B (ρ a x) (ρ a y) = B x y) :
    ∃ e : B.IsometryEquiv (Matrix.PSp4Three.form (n := n) (F := ZMod 2)),
      ∃ φ : A →* Matrix.PSp4Three.Sp n (ZMod 2), Function.Injective φ ∧
        ∀ a x, (φ a).val *ᵥ (e x) = e (ρ a x) := by
  obtain ⟨e⟩ := Matrix.PSp4Three.exists_isometry n B hAlt hN hd
  let σ : Representation (ZMod 2) A (Matrix.PSp4Three.Vector n (ZMod 2)) :=
    e.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  let f := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp σ
  have hpres (a : A) : f a ∈ Matrix.symplecticGroup (Fin n) (ZMod 2) := by
    apply Matrix.PSp4Three.mem_iff_preserves.mpr
    intro x y
    change Matrix.PSp4Three.form ((LinearMap.toMatrix' (σ a)) *ᵥ x)
      ((LinearMap.toMatrix' (σ a)) *ᵥ y) = _
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    change Matrix.PSp4Three.form (e (ρ a (e.symm x))) (e (ρ a (e.symm y))) = _
    rw [e.map_app, hB]
    exact (e.map_app (e.symm y) (e.symm x)).symm.trans (by simp)
  let fSp : A →* Matrix.PSp4Three.Sp n (ZMod 2) := f.codRestrict _ hpres
  have hfinj : Function.Injective fSp := by
    intro a b he
    apply hf
    apply e.toLinearEquiv.conjRingEquiv.injective
    apply LinearMap.toMatrixAlgEquiv'.injective
    exact congrArg Subtype.val he
  refine ⟨e, fSp, hfinj, ?_⟩
  intro a x
  change (LinearMap.toMatrix' (σ a)) *ᵥ (e x) = _
  rw [LinearMap.toMatrix'_mulVec]
  change e (ρ a (e.symm (e x))) = _
  exact congrArg (fun z => e (ρ a z)) (e.toLinearEquiv.symm_apply_apply x)
end BinaryPolarity
