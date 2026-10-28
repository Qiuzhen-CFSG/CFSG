module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedSubgroups
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.ReflectionWords

/-!
# Ambient D4 opposition from actual simple-reflection lifts

The explicit product constructed in `AmbientNormalizer.ReflectionWords`
simultaneously inverts the supplied torus. Its four ambient simple-reflection
lifts remain explicit inputs here. Unconditional existence and torus
self-centralization still require geometric proofs from `Geometry`.

This module is independent of the graph-field exponent and imports no
fixed-opposition assembly. Source: GLS3, Chapter 1, Remark 1.8.9 and
Theorem 1.9.5(e,f); Steinberg, Section 12.4 in
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition
open Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Conditional assembly of one simultaneous ambient inverter. Construction
of the four actual simple-reflection lifts must be discharged separately. -/
theorem exists_ambient_inverter_of_simple_reflections (S : Geometry K)
    (D : AmbientNormalizer.SimpleReflectionLifts S) :
    ∃ r : Variety.Point K, ∀ t ∈ S.torus, r * t * r⁻¹ = t⁻¹ :=
  ⟨D.oppositionRepresentative, D.oppositionRepresentative_inverts⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition
