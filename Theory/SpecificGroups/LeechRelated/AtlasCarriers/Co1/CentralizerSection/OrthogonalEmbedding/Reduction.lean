module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.Roots
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.LineTransport

/-!
# Reduction of the Co₁ elementary embedding to concrete certificates

The six Siegel matrices and singular-vector transport imply containment of the
actual elementary orthogonal subgroup in the literal local matrix image.
The coordinate representation is faithful, so restricting it gives an injective
homomorphism into `SmallCarrier`. Both finite certificate premises remain explicit
here; this module does not assert that those certificates have been supplied.

The resulting homomorphism has exactly the type consumed by
`CFSG.Quasithin.ChapterA.LeechSections.Co1.classicalQuotientDataOfEmbedding`.
Source purpose: Aschbacher–Smith A.2.19 and GLS3 Table 5.3l.
-/

@[expose] public noncomputable section
namespace Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
open ClassicalOrthogonal

/-- The exact two computational premises of the embedding. -/
def SixRoots : Prop := ∀ i : Fin 6, matrixHom (rootGenerator i) ∈ smallGenerated

def SingularTransport : Prop := ∀ u : V, u ≠ 0 → Q u = 0 →
  ∃ g : O, matrixHom g ∈ smallGenerated ∧ g.val e0 = u

theorem elementary_mem (hr : SixRoots) (ht : SingularTransport) :
    elementarySubgroup Q ≤ smallGenerated.comap matrixHom := by
  apply elementary_le_of_siegel_and_transport Q (smallGenerated.comap matrixHom) e0
    (formD_e 0)
  · intro v hv
    exact root_mem_of_six (smallGenerated.comap matrixHom) hr v hv
  · exact ht

def omegaEmbeddingOfCertificates (hr : SixRoots) (ht : SingularTransport) :
    OmegaPlus 4 (ZMod 2) →* SmallCarrier :=
  (matrixHom.comp (elementarySubgroup Q).subtype).codRestrict smallGenerated
    (fun g => elementary_mem hr ht g.prop)

theorem omegaEmbeddingOfCertificates_injective (hr : SixRoots) (ht : SingularTransport) :
    Function.Injective (omegaEmbeddingOfCertificates hr ht) := by
  intro a b h
  apply Subtype.ext
  apply matrixHom_injective
  exact congrArg Subtype.val h

end Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
