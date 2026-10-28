module

public import Theory.Character.AlternatingSix.Rational
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InflatedCharacters

/-!
# Applying the rational permutation construction to the normalizer

The rational character producer comes from genuine permutation representations
and the norm-one realization theorem. This adapter supplies that producer to
the literal normalizer quotient assembly. The checked finite permutation
calculations and A6 conjugacy separation discharge the rational input. Only
the independent golden character producer remains explicit in the final
adapter; the normalizer assembly owner supplies it.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
Section 6, pp.10–11.
-/

noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
open Theory.Character.AlternatingSix RationalConstruction

universe u
variable {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)

/-- Apply the actual permutation-character construction to the normalizer
quotient, keeping the two finite A6 inputs and the golden producer explicit. -/
public theorem normalizerInflatedBlock_of_alternatingSix_permutation_calculations
    (L : LocalAnalysisData D k) (Q : NormalizerClassData D k)
    (calculations : PermutationCalculations) (separation : OtherThreeSeparation)
    (golden : ∀ c μ : alternatingGroup (Fin 6), orderOf c = 3 → orderOf μ = 5 →
      RationalBlock c → Nonempty (GoldenBlock μ)) :
    Nonempty (NormalizerInflatedBlock Q) :=
  normalizerInflatedBlock_of_alternatingSix_blocks D k L Q
    (rationalBlock_of_permutation_calculations calculations separation) golden

/-- Supply the four rational A6 characters to the actual normalizer quotient
assembly. Only the golden producer remains, owned by the independent
degree-eight construction and discharged by the final normalizer assembly. -/
public theorem normalizerInflatedBlock_of_alternatingSix_golden
    (L : LocalAnalysisData D k) (Q : NormalizerClassData D k)
    (golden : ∀ c μ : alternatingGroup (Fin 6), orderOf c = 3 → orderOf μ = 5 →
      RationalBlock c → Nonempty (GoldenBlock μ)) :
    Nonempty (NormalizerInflatedBlock Q) :=
  normalizerInflatedBlock_of_alternatingSix_blocks D k L Q rationalBlock_nonempty golden

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
