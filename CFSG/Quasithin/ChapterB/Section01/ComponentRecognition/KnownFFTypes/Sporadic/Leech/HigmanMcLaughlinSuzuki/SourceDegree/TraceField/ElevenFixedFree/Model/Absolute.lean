module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.ElevenFixedFree.Model
public import Theory.Representation.HigmanSims.Twenty.Absolute

/-!
# HS model assembly with absolute irreducibility discharged

The literal ATLAS matrix action is now proved absolutely irreducible by
its checked rank-one density certificate. Applying the existing model
assembly leaves only the marked comparison with the degree-100 carrier
explicit, and retains the source-inherited simplicity hypothesis.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, p.16; ATLAS HSG1-p100B0 and HSG1-f2r20B0.
The construction of the marked comparison and final model assembly belong
to the separate carrier-comparison development.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Model

open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.Twenty

/-- The concrete model, conditional only on the actual marked carrier comparison. -/
theorem exists_model_of_markedComparison [IsSimpleGroup Carrier]
    (C : MarkedComparison) :
    ∃ ρ : Representation (ZMod 2) Carrier Vector,
      Function.Injective ρ ∧
        Representation.IsAbsolutelyIrreducible (F := ZMod 2) (G := Carrier) (V := Vector) ρ ∧
        Module.finrank (ZMod 2) Vector = 20 ∧
        ∀ g, orderOf g = 11 → LinearMap.ker (ρ g - 1) = ⊥ :=
  exists_model_of_inputs C absolutelyIrreducible

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Model
