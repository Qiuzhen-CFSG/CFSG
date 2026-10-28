module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights
public import Theory.Representation.Triality.RestrictedWeights

/-!
# D4 degree bounds with left characters

The same four normalizer representatives give the same reflections, because
reflection commutes with negation. This conditional bridge retains the actual
normalizer equations and weight occurrence. It proves the unchanged 8/24
bounds, without asserting the missing geometry or occurrence hypotheses.
Source: GLS3 §§1.14 and 2.8; Aschbacher--Smith, printed p.356.
-/

public section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Formal inversion preserves the complete conditional dimension bound. -/
theorem left_basic_finrank_lower_bounds_of_conjugation (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (g : Fin 4 → Variety.Point K)
    (c : Fin 4 → Variety.Point S.torus.carrierVariety → Variety.Point S.torus.carrierVariety)
    (hconj : ∀ i t, S.torus.includePoint t * g i = g i * S.torus.includePoint (c i t))
    (hraw : ∀ i a t, (S.weightEmbedding (reflection i a)).pointCharacter t =
      (S.weightEmbedding a).pointCharacter (c i t))
    (a : BasicWeight) (ha : weightSpace ρ S.torus (S.leftWeightEmbedding (coefficient a)) ≠ ⊥)
    (hne : a ≠ zeroWeight) :
    8 ≤ Module.finrank k V ∧ (diagramAction a = a → 24 ≤ Module.finrank k V) :=
  d4_basic_finrank_lower_bounds_of_conjugation ρ S.torus S.leftWeightEmbedding g c hconj
    (S.leftWeightEmbedding_reflection c hraw) a ha hne

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
