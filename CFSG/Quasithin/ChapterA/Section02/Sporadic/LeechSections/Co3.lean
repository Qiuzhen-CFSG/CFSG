module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.Quotient
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerQuotientOperations
public import CFSG.Quasithin.ClassicalModels

/-!
# The fixed Co₃ centralizer quotient for A.2.19

The checked permutation words supply an involution and a centralizing subgroup
in the fixed degree-276 Co₃ carrier. Its action on the 36 fixed points, compared
with the faithful symplectic action on even quadratic refinements, supplies an
unconditional surjection onto the literal `ClassicalGroup.PSp 3 (ZMod 2)`.
The kernel is normal inside the numerator. This supplies the section required
from the nonsplit `2Sp₆(2)` centralizer in GLS3 Table 5.3j.

Source: Aschbacher--Smith A.2.19, printed pp.40--41, which applies A.2.15(3)
to a nonabelian simple section of an involution centralizer.
Simplicity and rank obstructions for the target are separate ingredients of
the sporadic exclusion.
-/

public section
namespace CFSG.Quasithin.ChapterA.Sporadic.LeechSections

open _root_.Sporadic.LeechRelated
open Co3.CentralizerSection

/-- A genuine quotient of a centralizing subgroup in the unchanged ATLAS carrier. -/
def co3PointQuotientData : InvolutionCentralizerQuotientData Co3.Carrier pointGroup where
  involution := involution
  involution_order := involution_order
  numerator := numerator
  centralizes := numerator_centralizes
  quotientMap := pointQuotient
  surjective := pointQuotient_surjective

/-- The general comparison interface, retained for its existing consumers. -/
noncomputable def co3QuotientDataOfLinearAction
    (ρ : LinearData.Sp →* Equiv.Perm (Fin 36))
    (hρ : Function.Injective ρ)
    (hvalues : ∀ i, ρ (LinearData.generator i) = Tables.pointGenerator i)
    (hgenerate : Subgroup.closure (Set.range LinearData.generator) = ⊤) :
    InvolutionCentralizerQuotientData Co3.Carrier (ClassicalGroup.PSp 3 (ZMod 2)) where
  involution := involution
  involution_order := involution_order
  numerator := numerator
  centralizes := numerator_centralizes
  quotientMap := symplecticQuotientMap ρ hρ hvalues hgenerate
  surjective := symplecticQuotientMap_surjective ρ hρ hvalues hgenerate

/-- The Co₃ centralizer quotient, with every matrix premise discharged. -/
noncomputable def co3QuotientData :
    InvolutionCentralizerQuotientData Co3.Carrier (ClassicalGroup.PSp 3 (ZMod 2)) where
  involution := involution
  involution_order := involution_order
  numerator := numerator
  centralizes := numerator_centralizes
  quotientMap := quotientMap
  surjective := quotientMap_surjective

/-- The classical section is the quotient by the actual action's kernel. -/
noncomputable def co3CentralizerSectionEquiv :
    co3QuotientData.numerator ⧸ co3QuotientData.quotientMap.ker ≃*
      ClassicalGroup.PSp 3 (ZMod 2) :=
  co3QuotientData.quotientEquiv

end CFSG.Quasithin.ChapterA.Sporadic.LeechSections
