module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.Existence.Residual
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.Existence.ThreeValue
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.Existence.FirstThree
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiPairings
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.FourthMultiplicity

/-!
# Construction of the degree-21 irreducible

The local analysis proves the Suzuki pairings and hence unit multiplicities.
The certified calculation for the first three exceptional inductions supplies
their compatibility. The negative residual Gram entry then constructs a
genuine irreducible, and subgroup restriction completes its seven local values.
Only the actual special induction data remain an explicit conditional input;
their construction belongs to the normalizer-induction prerequisite of the
source-theorem assembly.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6–7, pp.12–16,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
open LocalModelDichotomy CharacterOrder

/-- The compatibility calculation is the only additional premise of the
construction; the actual irreducible and all local values are produced here. -/
public theorem exists_irreducible_of_firstThreeCompatible
    {G : Type*} [Group G] [Finite G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (I : SpecialInductionData D k)
    (hcompat : FirstThreeCompatible I) :
    ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ HasLocalValues D k χ := by
  have hI := hasSuzukiPairings_of_localAnalysis D k L I
  have hu := hasUnitMultiplicities D k L I hI
  obtain ⟨χ, hχ, hd, hv⟩ := exists_special_values_of_compatible D k L I hcard hu hcompat
  refine ⟨χ, hχ, local_values_of_special_values D k L hχ ?_ hv⟩
  simpa only [hd, Nat.cast_ofNat] using hχ.degree_eq

/-- The source-level local hypotheses discharge the compatibility premise and
produce the actual irreducible character with its values at the marked
elements. The Sylow-three normalizer hypothesis is retained in this interface
because it is part of the recognition theorem's source assumptions; the
compatibility calculation itself is stronger and does not need it. -/
public theorem exists_irreducible_of_local_analysis
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) (hcard : Nat.card G = 443520)
    (_hN3 : ∀ P : Sylow 3 G,
      Nat.card (Subgroup.normalizer (P : Set G)) = 72)
    (I : SpecialInductionData D k) :
    ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ HasLocalValues D k χ := by
  exact exists_irreducible_of_firstThreeCompatible D k L hcard I
    (firstThreeCompatible D k L hcard I)

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
