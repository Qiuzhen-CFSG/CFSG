module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives.OrbitReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives.CoordinateImage
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives.BinaryRecognition

/-!
# Janko's normalizer quotient has order 168 or is isomorphic to A₆

Sylow conjugacy realizes the initial fusion inside N(E). The six local
conjugates of printed z₃ then exclude quotient orders 24, 72, and 120,
leaving 168 or 360. The quotient is faithfully realized in the automorphism
group of the binary four-space, with image containing the exact
parity-twisted S₄ action. In the order-360 case, `BinaryRecognition` proves
that this image preserves the distinguished alternating form, embeds it in
the actual Sp₄(2) ≃ S₆, and identifies its index-two image with A₆.

The final theorem discharges the recognition premise of the retained
conditional interface. This route needs no assumed odd-core or local
normalizer condition. Excluding order 168 and proving the splitting clause
of the full source lemma belong to the later source assembly.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, pp.5–6.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Conditional assembly from a recognition theorem for the concrete
binary action. The order and the action inclusion are discharged here. -/
public theorem eNormalizerQuotient_alternatives_of_binary_recognition
    (hz3 : IsConj D.z (CaseII.into D k (CaseII.z 2)))
    (recognize : ∀ X : Subgroup (MulAut BinaryFour),
      twistedAction.range ≤ X → Nat.card X = 360 →
        Nonempty (X ≃* alternatingGroup (Fin 6))) :
    Nat.card (CaseII.eNormalizerQuotient D k) = 168 ∨
      Nonempty (CaseII.eNormalizerQuotient D k ≃* alternatingGroup (Fin 6)) := by
  rcases CaseII.eNormalizerQuotient_card_cases_of_z3 D k hz3 with h | h
  · exact Or.inl h
  · obtain ⟨e⟩ := recognize (CaseII.eNormalizerBinaryImage D k)
      (CaseII.twistedAction_le_eNormalizerBinaryImage D k)
      ((CaseII.eNormalizerBinaryImage_card D k).trans h)
    exact Or.inr ⟨(CaseII.eNormalizerQuotientEquivBinaryImage D k).trans e⟩

/-- From the ambient fusion of printed z₁ with z₃, the literal quotient
N(E)/E has order 168 or is isomorphic to the alternating group on six letters. -/
public theorem eNormalizerQuotient_alternatives [IsSimpleGroup G]
    (hz3 : IsConj D.z (CaseII.into D k (CaseII.z 2))) :
    Nat.card (CaseII.eNormalizerQuotient D k) = 168 ∨
      Nonempty (CaseII.eNormalizerQuotient D k ≃* alternatingGroup (Fin 6)) :=
  eNormalizerQuotient_alternatives_of_binary_recognition D k hz3
    BinaryRecognition.equiv_alternatingSix_of_card360

end Theory.GroupTheory.HeldM22A10.M22Identification
