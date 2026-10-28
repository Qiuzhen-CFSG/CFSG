module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerQuotientOperations

/-!
# The actual Suz centralizer action used by A.2.19

The checked involution and centralizing subgroup give an unconditional section
onto the exact 27-point permutation group. The proved equivalence of that image
with `PΩ⁻₆(2)` supplies the desired canonical quotient. Thus `quotientData`
discharges the Suz centralizer-section construction in the first elimination
step of A.2.19, with no extra local-structure or model-comparison premise.
Simplicity and rank facts for the target belong to the separate classical-section
development; this module does not assert the full sporadic exclusion.

Source: Aschbacher--Smith A.2.19, printed pp.40--41, and GLS3 Table 5.3o.
The fixed carrier is sporadic Suz, not its central cover or a Suzuki Lie group.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterA.SuzCentralizerSection
open Sporadic.LeechRelated.Suz
open Sporadic.LeechRelated.Suz.CentralizerSection

/-- The fully constructed section onto the literal 27-pair action image. -/
noncomputable def blockQuotientData : InvolutionCentralizerQuotientData Carrier BlockGroup where
  involution := involution
  involution_order := involution_order
  numerator := numerator
  centralizes := numerator_centralizes
  quotientMap := blockAction
  surjective := blockAction_surjective

/-- Transport the concrete block action along any actual canonical model comparison. -/
noncomputable def quotientDataOfEquiv
    (e : BlockGroup ≃* ClassicalGroup.POmegaMinus 3 (ZMod 2)) :
    InvolutionCentralizerQuotientData Carrier (ClassicalGroup.POmegaMinus 3 (ZMod 2)) :=
  blockQuotientData.mapTarget e

/-- The constructed Suz centralizer section onto the canonical `PΩ⁻₆(2)`. -/
noncomputable def quotientData :
    InvolutionCentralizerQuotientData Carrier (ClassicalGroup.POmegaMinus 3 (ZMod 2)) where
  involution := involution
  involution_order := involution_order
  numerator := numerator
  centralizes := numerator_centralizes
  quotientMap := quotientMap
  surjective := quotientMap_surjective

end CFSG.Quasithin.ChapterA.SuzCentralizerSection
