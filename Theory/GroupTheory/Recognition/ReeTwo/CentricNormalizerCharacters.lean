module

public import Theory.GroupTheory.Recognition.ReeTwo.CentricNormalizerSetup
public import Theory.GroupTheory.Recognition.ReeTwo.CentricNormalizerReduction
public import Theory.GroupTheory.Recognition.ReeTwo.FirstParabolicCharacter

/-!
# Ree two centric normalizer characters

The re-exported setup transports the two nontrivial alternative characters
and proves that both respect normalizers contained in the distinguished
involution centralizer. It also specifies the exact centric extremal
normalizer condition and the subgroup `C_S(Z₂(S))` for the remaining analysis.

The actual first-parabolic normalizer action selects one of the two
characters, and the centric-normalizer reduction then promotes that choice to
all centric extremal normalizers.

Source: van Beek (2024), Proposition 3.1, p. 10. The computation cited there
must be replaced by proofs for the verified Ree two model.
-/

namespace ReeTwo

/-- A common nontrivial binary character for the actual centric normalizers. -/
public theorem exists_common_centricNormalizer_character
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hz : orderOf z = 2)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) :
    ∃ χ : SylowModel →* FiveFour.Cyclic 2,
      (∃ x, χ x ≠ 1) ∧
        CentricNormalizerInvariant S (sylowEquivOfCentralizer S z hcentral ec) χ := by
  obtain hcore | hmixed :=
    alternativeCharacters_respect_firstParabolicNormalizer_of_centralizer S z hcentral ec
  · refine ⟨SylowModel.coreCharacter, ⟨SylowModel.root 1,
      SylowModel.coreCharacter_nontrivial⟩, ?_⟩
    exact alternativeCharacter_centricNormalizerInvariant_of_classification
      S z hz hcentral ec SylowModel.coreCharacter (Or.inl rfl) hcore
  · refine ⟨SylowModel.mixedCharacter, ⟨SylowModel.root 1,
      SylowModel.mixedCharacter_nontrivial⟩, ?_⟩
    exact alternativeCharacter_centricNormalizerInvariant_of_classification
      S z hz hcentral ec SylowModel.mixedCharacter (Or.inr rfl) hmixed

end ReeTwo
