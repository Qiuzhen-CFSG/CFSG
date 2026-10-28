module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.WordConstruction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Comparison

/-!
# D4 coroot words from actual rank-one charts

The comparison module proves all Cartan normalization and stored-coroot
identities, preserving the source convention `n(1)⁻¹ n(z)`. This assembly
chooses the four geometric charts once and obtains words valid at every
parameter. Existence of the charts remains an explicit prerequisite of this
conditional theorem; unconditional coroot-word existence is not asserted.

Sources: GLS3, `refs/KGroup/GLS3/Chapter1.tex`, Theorem 1.9.5(d),
Remarks 1.9.6 and the defining formulas of Theorem 1.12.1.
-/

public section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization

open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Four geometric charts suffice for the actual simple-coroot word data.
The chart-existence premise must still be discharged in final assembly. -/
theorem nonempty_simpleCorootWordData_of_charts (S : Geometry K)
    (h : ∀ i, Nonempty (SimpleRootSL2Chart S i)) : Nonempty (SimpleCorootWordData S) :=
  ⟨simpleCorootWordData_of_charts S (fun i => Classical.choice (h i))⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
