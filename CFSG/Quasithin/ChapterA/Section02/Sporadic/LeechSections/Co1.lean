module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerQuotientOperations

/-!
# The fixed Co₁ local quotient and its classical-section adapter

`binaryQuotientData` is constructed from the literal ATLAS words and their
checked eight-dimensional matrix action. The checked Siegel words and
singular-vector transport embed the actual elementary orthogonal group in
this concrete image. Pull back the embedding's range, invert the embedding
onto its range, and apply the scalar quotient. This constructs the Ω₈⁺(2)
section needed from GLS3 Table 5.3l.

`classicalQuotientData` discharges the embedding premise of the preserved
`classicalQuotientDataOfEmbedding` interface. `classicalSectionEquiv` identifies
the quotient by the kernel, normal inside the constructed numerator, with
the literal projective elementary orthogonal carrier. Simplicity and rank
properties of the target remain separate ingredients of A.2.19.

Source: Aschbacher--Smith, A.2.19, printed pp.40--41 of `refs/quasithin.pdf`,
and GLS3 Table 5.3l in `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterA.LeechSections.Co1

open Sporadic.LeechRelated.Co1
open CentralizerSection

/-- The checked eight-dimensional quotient of an actual involution centralizer. -/
def binaryQuotientData : InvolutionCentralizerQuotientData Carrier SmallCarrier where
  involution := z
  involution_order := z_order
  numerator := CentralizerSection.numerator
  centralizes := numerator_centralizes
  quotientMap := CentralizerSection.quotientMap
  surjective := quotientMap_surjective

/-- Pull back an actual elementary orthogonal subgroup of the computed image,
then take its scalar quotient. -/
def classicalQuotientDataOfEmbedding
    (f : ClassicalOrthogonal.OmegaPlus 4 (ZMod 2) →* SmallCarrier)
    (hf : Function.Injective f) :
    InvolutionCentralizerQuotientData Carrier (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) := by
  let d := binaryQuotientData.restrictTarget f.range
  let e := MonoidHom.ofInjective hf
  let p := ClassicalOrthogonal.projectiveElementaryMap
    (ClassicalOrthogonal.formD 4 (ZMod 2))
  exact
    { involution := d.involution
      involution_order := d.involution_order
      numerator := d.numerator
      centralizes := d.centralizes
      quotientMap := p.comp (e.symm.toMonoidHom.comp d.quotientMap)
      surjective := (ClassicalOrthogonal.projectiveElementaryMap_surjective
        (ClassicalOrthogonal.formD 4 (ZMod 2))).comp
          (e.symm.surjective.comp d.surjective) }

/-- The unconditional orthogonal quotient of an actual Co₁ involution centralizer. -/
def classicalQuotientData :
    InvolutionCentralizerQuotientData Carrier (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) :=
  classicalQuotientDataOfEmbedding omegaEmbedding omegaEmbedding_injective

/-- The section uses the relatively normal kernel of the constructed quotient map. -/
def classicalSectionEquiv :
    classicalQuotientData.numerator ⧸ classicalQuotientData.quotientMap.ker ≃*
      ClassicalOrthogonal.POmegaPlus 4 (ZMod 2) :=
  classicalQuotientData.quotientEquiv

end CFSG.Quasithin.ChapterA.LeechSections.Co1
