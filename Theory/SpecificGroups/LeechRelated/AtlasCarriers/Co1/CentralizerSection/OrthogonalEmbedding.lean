module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.RootCertificates
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.TransportCertificates

/-!
# The elementary orthogonal embedding in the Co₁ local image

The six checked Siegel words generate the root subgroup at e₀. The checked
singular-vector orbit transports this root subgroup to every nonzero singular
vector; covariance and the definition of the elementary group give containment.
The faithful coordinate representation therefore restricts to an injective
homomorphism from the exact Ω₈⁺(2) carrier into `SmallCarrier`.

`omegaEmbedding_action` identifies the resulting map with its actual matrix
representation in the ordered coordinates e0,e1,e2,e3,f0,f1,f2,f3. No group-order,
simplicity, or equality-of-generated-groups assertion is needed. This is the
embedding consumed by the parent Co₁ centralizer quotient construction.

Source: Aschbacher–Smith A.2.19, printed pp.40–41, and GLS3 Table 5.3l.
-/

@[expose] public noncomputable section
namespace Sporadic.LeechRelated.Co1.CentralizerSection
open scoped Matrix

/-- The actual elementary orthogonal subgroup of the computed local matrix image. -/
def omegaEmbedding : ClassicalOrthogonal.OmegaPlus 4 (ZMod 2) →* SmallCarrier :=
  OrthogonalEmbedding.omegaEmbeddingOfCertificates
    OrthogonalEmbedding.sixRoots OrthogonalEmbedding.singularTransport

theorem omegaEmbedding_injective : Function.Injective omegaEmbedding :=
  OrthogonalEmbedding.omegaEmbeddingOfCertificates_injective
    OrthogonalEmbedding.sixRoots OrthogonalEmbedding.singularTransport

/-- The embedding is exactly the hyperbolic-coordinate matrix representation. -/
theorem omegaEmbedding_action (g : ClassicalOrthogonal.OmegaPlus 4 (ZMod 2))
    (v : ClassicalOrthogonal.VectorD 4 (ZMod 2)) :
    (omegaEmbedding g).val.val *ᵥ OrthogonalEmbedding.coordinates v =
      OrthogonalEmbedding.coordinates (g.val.val v) :=
  OrthogonalEmbedding.matrixHom_action g.val v

end Sporadic.LeechRelated.Co1.CentralizerSection
