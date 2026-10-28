module

public import Theory.AlgebraicGroup.Automorphisms.Lang.Basic
public import Theory.AlgebraicGroup.Automorphisms.Steinberg
public import Theory.AlgebraicGroup.Dimension.Fiber
public import Theory.AlgebraicGroup.Irreducible.Product

universe u

/-!
# Finite-fiber dominance for the Lang morphism

For an algebraic-group endomorphism `σ`, nonempty fibers of the regular Lang
morphism `g ↦ g * σ(g⁻¹)` inject into the fixed-point subtype of `σ`, so finite
fixed points make every fiber finite.  If the ambient group is connected, it is
irreducible; the equal-dimension finite-fiber criterion then makes the Lang
image dense, and constructibility supplies a nonempty open subset contained in
that image.

This is the geometric implication in Steinberg, *Endomorphisms of Linear
Algebraic Groups*, Theorem 10.2, used toward GLS3, Chapter 2, Theorem 2.1.1.
Full Lang surjectivity additionally uses Steinberg's solvable and semisimple
reductions (Theorems 10.4--10.8); density alone does not imply surjectivity.
-/

namespace Theory.AlgebraicGroup

open Topology

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Every Lang fiber is finite when the fixed-point subtype is finite. -/
public theorem langMorphism_finite_fiber
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσfixed : Finite {x : Variety.Point K | σ.onPoints x = x})
    (y : Variety.Point K) :
    Set.Finite {g : Variety.Point K | (langMorphism σ).toFun g = y} := by
  rw [← Set.finite_coe_iff]
  classical
  by_cases hnonempty : Nonempty
      {g : Variety.Point K | (langMorphism σ).toFun g = y}
  · let a := Classical.choice hnonempty
    let fiberToFixed :
        {g : Variety.Point K | (langMorphism σ).toFun g = y} →
          {x : Variety.Point K | σ.onPoints x = x} :=
      fun g => ⟨a.1⁻¹ * g.1, by
        have ha := a.2
        change a.1 * σ.onPoints a.1⁻¹ = y at ha
        have hg := g.2
        change g.1 * σ.onPoints g.1⁻¹ = y at hg
        have hfixed := congrArg
          (fun z => a.1⁻¹ * z * σ.onPoints g.1) (ha.trans hg.symm)
        have hfixed' :
            σ.onPoints a.1⁻¹ * σ.onPoints g.1 = a.1⁻¹ * g.1 := by
          simpa [mul_assoc] using hfixed
        calc
          σ.onPoints (a.1⁻¹ * g.1) =
              σ.onPoints a.1⁻¹ * σ.onPoints g.1 := by
                rw [σ.onPoints.map_mul]
          _ = a.1⁻¹ * g.1 := hfixed'⟩
    exact Finite.of_injective fiberToFixed (by
      intro g h hgh
      apply Subtype.ext
      exact mul_left_cancel (congrArg Subtype.val hgh))
  · let fiberToFixed :
        {g : Variety.Point K | (langMorphism σ).toFun g = y} →
          {x : Variety.Point K | σ.onPoints x = x} :=
      fun _ => ⟨1, by simp⟩
    exact Finite.of_injective fiberToFixed (by
      intro g _ _
      exact False.elim (hnonempty ⟨g⟩))

/-- Finite fixed points make the Lang image dense in a connected algebraic
group.  Surjectivity of `σ` is not needed for this geometric implication. -/
public theorem langMorphism_denseRange_of_finite_fixed
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσfixed : Finite {x : Variety.Point K | σ.onPoints x = x})
    (hK : Variety.IsConnected K) :
    Dense (Set.range (langMorphism σ).toFun) := by
  let hKi := connectedAlgebraicGroup_irreducible K hK
  exact (langMorphism σ).denseRange_of_finite_fibers_of_dimension_eq
    hKi hKi rfl (langMorphism_finite_fiber σ hσfixed)

/-- The dense-image consequence for a Steinberg endomorphism. -/
public theorem langMorphism_denseRange
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : Variety.IsConnected K) :
    Dense (Set.range (langMorphism σ).toFun) :=
  langMorphism_denseRange_of_finite_fixed σ hσ.2 hK

/-- The Lang image contains a nonempty open subset in the connected
finite-fixed-point setting. -/
public theorem langMorphism_exists_nonempty_open_subset_range
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : Variety.IsConnected K) :
    ∃ U : Set (Variety.Point K),
      IsOpen U ∧ U.Nonempty ∧ U ⊆ Set.range (langMorphism σ).toFun := by
  let hKi := connectedAlgebraicGroup_irreducible K hK
  let : PreirreducibleSpace (Variety.Point K) := ⟨hKi.2⟩
  exact (langMorphism σ).exists_nonempty_open_subset_range_of_dense
    (langMorphism_denseRange σ hσ hK)

end Theory.AlgebraicGroup
