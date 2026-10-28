module

public import Theory.Representation.HigmanSims.Twenty.Model
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.ElevenFixedFree.Model.Absolute
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.ElevenFixedFree.Model.Comparison
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.ElevenFixedFree.Transport

/-!
# The completed concrete HS degree-twenty model

Both construction inputs are discharged: the literal ATLAS matrices are
absolutely irreducible and the marked permutation-to-matrix homomorphism
is constructed. Inherited simplicity makes the action faithful. The
checked inverse of the displacement of `ab`, together with cyclic Sylow
conjugacy in the actual carrier, gives zero fixed space at every element
of order eleven.

The final theorem applies this named model to the existing universal
transport theorem. Only recognition of arbitrary absolute degree-twenty
representations remains explicit there; that separate source obligation
is `DegreeTwentyModelComparison carrierRepresentation`.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, p.16; ATLAS HSG1-p100B0 and HSG1-f2r20B0.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Model
universe v

open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.Twenty

/-- Every order-eleven element is fixed-point-free on the constructed action. -/
theorem orderEleven_fixedFree [IsSimpleGroup Carrier]
    (g : Carrier) (hg : orderOf g = 11) :
    LinearMap.ker (carrierRepresentation g - 1) = ⊥ :=
  orderEleven_fixedFree_constructed g hg

/-- The concrete faithful absolute degree-twenty model, with both construction
premises discharged and only the source-inherited simplicity retained. -/
theorem exists_model [IsSimpleGroup Carrier] :
    ∃ ρ : Representation (ZMod 2) Carrier Vector,
      Function.Injective ρ ∧
        Representation.IsAbsolutelyIrreducible (F := ZMod 2) (G := Carrier) (V := Vector) ρ ∧
        Module.finrank (ZMod 2) Vector = 20 ∧
        ∀ g, orderOf g = 11 → LinearMap.ker (ρ g - 1) = ⊥ :=
  ⟨carrierRepresentation, carrierRepresentation_injective,
    carrierRepresentation_absolutelyIrreducible, representation_finrank,
    orderEleven_fixedFree⟩

/-- The actual constructed model discharges the model premise of universal
fixed-space transport. The separate representation-recognition owner must
supply the displayed comparison with this particular action. -/
theorem degreeTwentyElevenFixedFree_of_constructedModelComparison
    (hcompare : DegreeTwentyModelComparison.{0,v} carrierRepresentation) :
    DegreeTwentyElevenFixedFree.{v} := by
  intro hs
  let : IsSimpleGroup Carrier := hs
  exact degreeTwentyElevenFixedFree_of_modelComparison carrierRepresentation
    orderEleven_fixedFree hcompare hs

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Model
