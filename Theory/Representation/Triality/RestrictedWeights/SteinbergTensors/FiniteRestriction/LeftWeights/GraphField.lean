module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Pullback

/-!
# Finite-geometry graph and graph-field character bridges

The concrete torus restrictions remain owned by the geometry producers.
Given their actual raw character or power equations, inversion supplies the
left formulas with the original forward and inverse diagram actions.
No rational or finite representation conclusion is assumed in these inputs.
Source: GLS3 2.8.3--4, 2.8.8, and Steinberg (6.1).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

theorem Geometry.leftWeightEmbedding_pullback_graph (S : Geometry K)
    (f : Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety)
    (hf : ∀ a, TorusCharacter.pullback f (S.coordinateEmbedding a) =
      S.coordinateEmbedding (a ∘ typeD4DiagramPermutation)) (a : BasicWeight) :
    TorusCharacter.pullback f (S.leftWeightEmbedding (coefficient a)) =
      S.leftWeightEmbedding (coefficient (diagramAction a)) :=
  S.leftWeightEmbedding_pullback f _ hf (coefficient a)

theorem Geometry.leftWeightEmbedding_pullback_inverseGraph (S : Geometry K)
    (f : Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety)
    (hf : ∀ a, TorusCharacter.pullback f (S.coordinateEmbedding a) =
      S.coordinateEmbedding (a ∘ typeD4DiagramPermutation.symm)) (a : BasicWeight) :
    TorusCharacter.pullback f (S.leftWeightEmbedding (coefficient a)) =
      S.leftWeightEmbedding (coefficient (inverseDiagramAction a)) := by
  rw [inverseDiagramAction_eq_pullback]
  exact S.leftWeightEmbedding_pullback f _ hf (coefficient a)

/-- Specialize `π` to the forward or inverse numbered permutation as appropriate. -/
theorem Geometry.leftWeightEmbedding_pullback_graphField (S : Geometry K)
    (graph frob : Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety)
    (π : Fin 4 → Fin 4) (n : ℕ)
    (hg : ∀ a, TorusCharacter.pullback graph (S.coordinateEmbedding a) =
      S.coordinateEmbedding (a ∘ π))
    (hf : ∀ t, frob.onPoints t = t ^ (2 ^ n)) (a : Weight) :
    TorusCharacter.pullback (graph.comp frob) (S.leftWeightEmbedding a) =
      S.leftWeightEmbedding ((2 ^ n : ℕ) • (a ∘ π)) := by
  change TorusCharacter.pullback frob
    (TorusCharacter.pullback graph (S.leftWeightEmbedding a)) = _
  rw [S.leftWeightEmbedding_pullback graph π hg]
  exact S.leftWeightEmbedding_pullback_power frob (2 ^ n) hf _

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
