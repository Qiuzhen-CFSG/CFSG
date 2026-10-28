module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Output

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

def shapeIndex (k : Nat) : Fin 1296 := ⟨min k 1295, by omega⟩

def shapeAt (k : Nat) : Bool := decide (∀ a : Letter Bool,
  facts (output (shapeIndex k) a) =
    ⟨survivor (shapeIndex k), [a], survivor (dest (shapeIndex k) a)⟩)

def shapeChunk (start count : Nat) : Bool :=
  (List.range count).all (fun k => shapeAt (start + k))

theorem shapeChunk_sound (start count : Nat)
    (hc : shapeChunk start count = true) (i : Fin 1296)
    (hlo : start ≤ i.val) (hhi : i.val < start + count) :
    ∀ a, facts (output i a) = ⟨survivor i, [a], survivor (dest i a)⟩ := by
  have hm : i.val - start ∈ List.range count := by simp only [List.mem_range]; omega
  have he := List.all_eq_true.mp hc (i.val - start) hm
  have hi : shapeIndex (start + (i.val - start)) = i := by
    apply Fin.ext
    simp only [shapeIndex]
    omega
  simpa only [shapeAt, decide_eq_true_eq, hi] using he

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
