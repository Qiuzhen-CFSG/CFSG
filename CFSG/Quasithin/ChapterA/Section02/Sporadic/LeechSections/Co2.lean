module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co2.CentralizerSection
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerQuotientOperations

/-!
# The Co₂ involution-centralizer section used by A.2.19

The checked permutation-word construction supplies an involution and a
centralizing subgroup surjecting onto the literal `ClassicalGroup.PSp 3
(ZMod 2)` matrix quotient. The first isomorphism theorem gives the quotient
by the kernel normal inside that subgroup. There is no ambient-normality,
splitting, order-recognition or additional local-structure hypothesis.

Source: Aschbacher–Smith A.2.19, printed pp. 40–41; GLS3 Table 5.3k,
the extraspecial-by-Sp₆(2) centralizer row. Simplicity and rank properties of
the target are separate ingredients of the sporadic exclusion.
-/

public section
namespace CFSG.Quasithin.ChapterA.LeechSections

open Sporadic.LeechRelated

/-- The actual Co₂ centralizer quotient needed in the sporadic exclusion. -/
noncomputable def co2CentralizerQuotient :
    InvolutionCentralizerQuotientData Co2.Carrier (ClassicalGroup.PSp 3 (ZMod 2)) where
  involution := Co2.CentralizerSection.z
  involution_order := Co2.CentralizerSection.z_order
  numerator := Co2.CentralizerSection.numerator
  centralizes := Co2.CentralizerSection.numerator_centralizes
  quotientMap := Co2.CentralizerSection.quotientMap
  surjective := Co2.CentralizerSection.quotientMap_surjective

/-- The section uses precisely the kernel of the constructed quotient action. -/
noncomputable def co2CentralizerSectionEquiv :
    co2CentralizerQuotient.numerator ⧸ co2CentralizerQuotient.quotientMap.ker ≃*
      ClassicalGroup.PSp 3 (ZMod 2) :=
  co2CentralizerQuotient.quotientEquiv

end CFSG.Quasithin.ChapterA.LeechSections
