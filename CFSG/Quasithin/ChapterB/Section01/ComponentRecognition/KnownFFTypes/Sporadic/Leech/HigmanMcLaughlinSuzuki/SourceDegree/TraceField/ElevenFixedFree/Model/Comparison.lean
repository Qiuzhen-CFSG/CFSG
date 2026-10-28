module

public import Theory.Representation.HigmanSims.Twenty.Comparison
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.ElevenFixedFree.Model

/-!
# Order-eleven fixed-point-freeness for the constructed HS action

The constructed marked comparison discharges the comparison premise of
`Model.orderEleven_fixedFree_of_markedComparison`. Simplicity is still the
source-inherited hypothesis used by that theorem. Absolute irreducibility and
final model assembly remain independent obligations of the model owner.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, p.16; ATLAS HSG1-p100B0 and HSG1-f2r20B0.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Model

open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.Twenty

/-- The comparison premise is discharged by the actual permutation-module construction. -/
theorem orderEleven_fixedFree_constructed [IsSimpleGroup Carrier]
    (g : Carrier) (hg : orderOf g = 11) :
    LinearMap.ker (Comparison.markedComparison.action g - 1) = ⊥ :=
  orderEleven_fixedFree_of_markedComparison Comparison.markedComparison g hg

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Model
