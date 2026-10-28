module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Actions.Bitplanes
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Actions.Networks.Data

/-!
# Independent bit-mask certificate contracts for the Fi23 loops

The fixed transforms have three separate obligations: their source-map
semantics, their shared-table semantics, and the coordinate masks' meaning.
Once these are certified, a loop needs only fifteen whole-mask equalities.
All maps act on the original carrier; the core comparison here is numerical
and does not assume or require the separate subgroup-word `CoreActions`.

Source: retained ATLAS F23G1-p31671B0 and GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

/-- Comparison with the two unchanged source generators. -/
def SourcePullbacks : Prop :=
  Pullback sourceA sourceATransform ∧ Pullback sourceB sourceBTransform

/-- Comparison with all the unchanged candidate tables, including the default. -/
def CorePullbacks : Prop := ∀ i, Pullback (coreMap i) (coreTransform i)

/-- Coordinates on the full padded set, also usable for total network semantics. -/
def CoordinateMaskSound : Prop := ∀ (k : Fin 15) (j : Nat), j < 32768 →
  (coordinateMasks k).testBit j = j.testBit k.val

theorem coordinateMask_separating (h : CoordinateMaskSound) : Separating coordinateMasks :=
  fun k x => h k x.val (Nat.lt_trans x.isLt (by decide))

/-- The exact loop square, checked simultaneously at every bit position. -/
def MaskEquation (i : Fin 722) (k : Fin 15) : Prop :=
  factorTransform coreTransform (factorLength i) (factorBits i)
    (pathTransform sourceATransform sourceBTransform (pathLength i) (pathBits i)
      (if i.val < 695 then sourceATransform (coordinateMasks k)
        else sourceBTransform (coordinateMasks k))) =
    pathTransform sourceATransform sourceBTransform (pathLength i) (pathBits i)
      (coordinateMasks k)

theorem actionCheck_of_certificate (hs : SourcePullbacks) (hc : CorePullbacks)
    (hp : CoordinateMaskSound) (i : Fin 722) (he : ∀ k, MaskEquation i k) :
    ∀ x, ActionCheck i x :=
  actionCheck_of_masks _ _ _ hs.1 hs.2 hc coordinateMasks (coordinateMask_separating hp) i he

/-- Actual consumer on the literal first-tree edge. Final assembly must supply
all three numerical semantics certificates; only `CoreActions` is independent. -/
theorem edge_mem_of_certificate (hcore : CoreActions)
    (hs : SourcePullbacks) (hc : CorePullbacks) (hp : CoordinateMaskSound)
    (i : Fin 722) (he : ∀ k, MaskEquation i k) :
    edge (loopGenerator i) (loopPoint i) ∈ KernelUpperData.first :=
  loop_edge_mem_of_masks hcore _ _ _ hs.1 hs.2 hc coordinateMasks
    (coordinateMask_separating hp) i he

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
