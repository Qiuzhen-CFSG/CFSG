module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.outputCode
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.destCode
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.repCode
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.Facts

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def output (n : Nat) : Nat := min (outputCode n) 49399

def destination (n : Nat) : Fin 4032 :=
  ⟨min (destCode n) 4031, by omega⟩

def shapeAt (n : Nat) : Bool :=
  factBEq (facts (output n)) ⟨repCode (n / 4), [decode (n % 4)], repCode (destination n).val⟩

def shapeChunk (start count : Nat) : Bool :=
  (List.range count).all fun k => shapeAt (start+k)

theorem shapeChunk_sound {start count : Nat} (h : shapeChunk start count = true)
    (n : Nat) (hlo : start ≤ n) (hhi : n < start+count) : shapeAt n = true := by
  have hm : n-start ∈ List.range count := by simp only [List.mem_range]; omega
  have hs := List.all_eq_true.mp h (n-start) hm
  have he : start + (n-start) = n := by omega
  rwa [he] at hs

theorem output_lt (n : Nat) : output n < 49400 :=
  Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
