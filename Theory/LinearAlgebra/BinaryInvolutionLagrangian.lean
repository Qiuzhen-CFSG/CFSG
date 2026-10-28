module

public import Theory.LinearAlgebra.BinaryLagrangianKernel
public import Mathlib.Order.Preorder.Finite

/-!
# A fixed Lagrangian for a binary symplectic involution

The image of t-1 is isotropic when t preserves an alternating form and
squares to one. Extend this image to a maximal isotropic subspace. Its
orthogonal complement equals itself, and the adjoint identity for t
shows that t fixes it pointwise.

This gives the involution representatives needed in Aschbacher–Smith
13.4.9, printed p.906, without assuming a classification of involutions.
-/

public noncomputable section

namespace Theory.LinearAlgebra
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Every binary symplectic involution fixes a Lagrangian pointwise. -/
theorem binary_involution_fixed_lagrangian (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hND : B.Nondegenerate)
    (t : V ≃ₗ[ZMod 2] V) (ht : ∀ x, t (t x) = x)
    (hp : ∀ x y, B (t x) (t y) = B x y) :
    ∃ W : Submodule (ZMod 2) V, B.orthogonal W = W ∧ ∀ x ∈ W, t x = x := by
  let N : Module.End (ZMod 2) V := t.toLinearMap - 1
  have hadj (x y : V) : B (t x) y = B x (t y) := by
    simpa only [ht] using hp x (t y)
  have hiso (x y : V) : B (N x) (N y) = 0 := by
    change B (t x - x) (t y - y) = 0
    rw [LinearMap.BilinForm.sub_left, map_sub, map_sub, hp, hadj]
    simp only [CharTwo.sub_eq_add, add_assoc, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero]
  let P : Set (Submodule (ZMod 2) V) :=
    {W | N.range ≤ W ∧ ∀ x ∈ W, ∀ y ∈ W, B x y = 0}
  have hP : P.Nonempty := ⟨N.range, le_rfl, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hiso x y⟩
  obtain ⟨W, hW, hmax⟩ := P.toFinite.exists_maximal hP
  have horth : B.orthogonal W = W := by
    apply le_antisymm
    · intro x hx
      let U : Submodule (ZMod 2) V := W ⊔ Submodule.span (ZMod 2) {x}
      have hU : U ∈ P := by
        refine ⟨hW.1.trans le_sup_left, ?_⟩
        intro u hu v hv
        obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
        obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu₂
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv₂
        have hxu : B x v₁ = 0 := hB.eq_iff.mp (hx v₁ hv₁)
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hW.2 u₁ hu₁ v₁ hv₁, hx u₁ hu₁, hxu, hB.self_eq_zero,
          smul_zero, add_zero]
      exact (hmax hU le_sup_left) (show x ∈ U from
        (show Submodule.span (ZMod 2) {x} ≤ U from le_sup_right)
          (Submodule.subset_span (by simp)))
    · intro x hx y hy
      exact hW.2 y hy x hx
  refine ⟨W, horth, ?_⟩
  intro x hx
  have hNx (y : V) : B y (N x) = 0 := by
    change B y (t x - x) = 0
    rw [map_sub, ← hadj]
    have hh := hW.2 (N y) (hW.1 ⟨y, rfl⟩) x hx
    change B (t y - y) x = 0 at hh
    simpa only [LinearMap.BilinForm.sub_left] using hh
  exact sub_eq_zero.mp (hND.2 (N x) hNx)

end Theory.LinearAlgebra
