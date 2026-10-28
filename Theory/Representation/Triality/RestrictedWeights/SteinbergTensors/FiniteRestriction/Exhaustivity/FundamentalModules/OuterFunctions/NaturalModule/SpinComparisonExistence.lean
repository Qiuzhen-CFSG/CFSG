module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.Comparison
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.LocalMaps

/-!
# Assembly of a regular D4-to-Spin comparison

A regular lift of a marked point homomorphism gives `SpinComparison`: the
four raw torus coordinates are retained, and surjectivity of each actual root
parametrization gives the required positive-root image condition. LocalMaps
constructs the regular restrictions on the torus and every root curve.

This is conditional assembly. Constructing the point homomorphism from
`Geometry` and proving its global regularity remain necessary before asserting
unconditional existence. The source identification is with the actual
Clifford Spin carrier, not just its orthogonal point group.

Source: GLS3 Theorem 1.10.7(d) and Example 1.14.9(d),
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg (6.1)--(6.2) and Section 13,
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
open Theory.AlgebraicGroup Triality.SimplyConnected

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A regular lift discharges the global geometric obligation for a given
marked point homomorphism. Existence of both inputs is still required. -/
theorem nonempty_spinComparison_of_rootwise_lift (S : Geometry K)
    (C : SpinComparisonExistence.RootwiseSpinHom k S)
    (f : Morphism K (groupVariety k)) (hf : f.onPoints = C.pointHom) :
    Nonempty (SpinComparison k S) := by
  refine ⟨⟨f, ?_, ?_⟩⟩
  · intro t
    rw [hf]
    exact C.torus t
  · intro r _ z
    rw [hf]
    exact C.root_image r z

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
