module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusData

/-!
# Integral lattice equations for twisted D4 torus kernels

The character lattice uses integral simple-coroot coordinates. A Weyl
representation is compatible with this marking precisely when its simple
reflections have the published Cartan-matrix formulas. Pullback along the
left action on torus points uses the inverse Weyl element. Consequently the
twisted character endomorphism is `q δ* - ρ(w⁻¹)`.

These definitions fix the common interface for the torus duality argument and
the independent determinant calculations. No determinant identity or kernel
cardinality is assumed by the definitions.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 14.4 and 14.8--14.9.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount

open Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight

/-- A linear action on the complete integral weight lattice. -/
abbrev WeightRepresentation := Weyl →* (Weight ≃ₗ[ℤ] Weight)

/-- Compatibility with the actual numbered simple reflections. -/
def ReflectionCompatible (ρ : WeightRepresentation) : Prop :=
  ∀ (i : Fin 4) (a : Weight),
    ρ (RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
      (typeDSimpleRootIndex 2 i)) a = reflection i a

/-- Pullback of integral weights by the specified diagram cycle. -/
def diagramWeightMap : Weight →ₗ[ℤ] Weight where
  toFun a := a ∘ typeD4DiagramPermutation
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The character equation for a graph-field twist and a Weyl element. -/
def twistedWeightMap (ρ : WeightRepresentation) (q : ℤ) (w : Weyl) :
    Weight →ₗ[ℤ] Weight :=
  q • diagramWeightMap - (ρ w⁻¹).toLinearMap

theorem twistedWeightMap_apply (ρ : WeightRepresentation) (q : ℤ)
    (w : Weyl) (a : Weight) :
    twistedWeightMap ρ q w a = q • (a ∘ typeD4DiagramPermutation) - ρ w⁻¹ a :=
  rfl

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount
