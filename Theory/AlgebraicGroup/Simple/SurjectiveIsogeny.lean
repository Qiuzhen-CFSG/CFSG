module

public import Theory.AlgebraicGroup.Morphism.FiniteKernel
public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Theory.AlgebraicGroup.Simple.Basic

/-! A point-surjective morphism between simple algebraic groups is an isogeny.

The kernel is a closed normal subgroup of the source. It cannot be the whole
source: surjectivity would then make the target's point group subsingleton,
contradicting the nontrivial derived subgroup required by simplicity. Source
simplicity therefore makes the kernel zero-dimensional, and the finite-kernel
criterion finishes the proof. This isolates the standard reduction used in the
surjective-morphism classification campaign.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k]

/-- A point-surjective morphism between simple algebraic groups is an isogeny. -/
public theorem surjective_morphism_isIsogeny_of_simple
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (hK : IsSimpleAlgebraicGroup K) (hH : IsSimpleAlgebraicGroup H)
    (f : AlgebraicGroup.Morphism K H)
    (hf : Function.Surjective f.onPoints) :
    IsIsogeny f := by
  refine ⟨hf, ?_⟩
  have hkernel_ne_top : f.kernelClosedSubgroup.toSubgroup ≠ ⊤ := by
    intro hkernel
    have hf_one (x : Variety.Point K) : f.onPoints x = 1 := by
      have hx : x ∈ f.kernelClosedSubgroup.toSubgroup := by
        rw [hkernel]
        trivial
      exact hx
    have hHsubsingleton : Subsingleton (Variety.Point H) := by
      constructor
      intro x y
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      rw [hf_one, hf_one]
    let _ := hHsubsingleton
    apply hH.2.1
    exact Subsingleton.elim _ _
  have hkernel_dimension :
      Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 :=
    hK.2.2 f.kernelClosedSubgroup f.kernelClosedSubgroup_isNormal hkernel_ne_top
  exact f.kernel_finite_of_kernelClosedSubgroup_dimension_eq_zero hkernel_dimension

end Theory.AlgebraicGroup
