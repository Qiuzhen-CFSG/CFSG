module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizerClassification
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution

/-!
# Completeness of the degree-ten binary M₁₁ module

Every faithful degree-ten binary representation of the actual M₁₁ is
equivalent to the restriction of the twelve-point augmentation quotient.
The normalizer classification first identifies the action of the literal
C₁₁:C₅. Coordinate transport fixes this action, and the certified involution
conjugacy then identifies the remaining generator. Faithfulness and degree
ten already imply irreducibility by the order-eleven bound.

The reference is compared equivariantly with the eleven-point augmentation
module by `augmentationEquivPoint`; it uses the actual M₁₁ inclusion in M₁₂.
The M₁₂ application below discharges the whole point-classification input.
Only rigidity of the extending M₁₂ action remains explicit there.

Source application: Aschbacher--Smith, G.7.3(2), printed p.348 (PDF p.359),
citing G. D. James, *The modular characters of the Mathieu groups*,
J. Algebra 27 (1973), 57--111. This supplies the smaller-group step in the
M₁₂ recognition proof, without assuming that recognition theorem.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification
open Sporadic.Mathieu

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every faithful degree-ten binary M₁₁ representation is the actual point
restriction of the M₁₂ heart. No irreducibility or extension premise is needed. -/
theorem equiv_point_of_faithful_degree_ten (σ : Representation (ZMod 2) M11 V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 10) :
    Nonempty (σ.Equiv pointRepresentation) :=
  equiv_point_of_normalizer_extension σ hf hd NormalizedInvolution.exists_equiv

/-- The literal point restriction of a faithful small M₁₂ representation has
the required M₁₁ equivalence, with all local classification premises discharged. -/
theorem point_restriction_equiv (ρ : Representation (ZMod 2) M12 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 10) :
    Nonempty (Representation.Equiv (ρ.comp pointEmbedding) pointRepresentation) :=
  equiv_point_of_faithful_degree_ten (ρ.comp pointEmbedding)
    (hf.comp pointEmbedding_injective) (finrank_eq_ten ρ hf hd)

/-- Apply M₁₁ completeness to M₁₂ recognition. The only remaining input is
rigidity of the full M₁₂ action extending its fixed point restriction. -/
theorem isM12Heart_of_point_extension (ρ : Representation (ZMod 2) M12 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 10)
    (hextension : ∀ τ : Representation (ZMod 2) M12 M12Heart,
      Function.Injective τ → τ.IsIrreducible →
      (∀ g : M11, τ (pointEmbedding g) = m12HeartRepresentation (pointEmbedding g)) →
      IsM12Heart τ) : IsM12Heart ρ :=
  isM12Heart_of_point_inputs ρ hf (point_restriction_equiv ρ hf hd) hextension

end Representation.MathieuSmall.M12Recognition.PointClassification
