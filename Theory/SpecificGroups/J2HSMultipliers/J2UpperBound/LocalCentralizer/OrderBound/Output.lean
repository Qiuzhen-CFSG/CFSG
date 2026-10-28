module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.outputCode
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.destCode
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.repCode
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.Facts
public import Theory.GroupTheory.CosetWordCertificateBoolean

/-! Kernel-checked coset certificate for the normalized J₂ centralizer presentation, the trivial subgroup.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
open Subgroup.CosetWordCertificate

def output (n : Nat) : Nat := min (outputCode n) 41124

def destination (n : Nat) : Fin 3840 :=
  ⟨min (destCode n) 3839, by omega⟩

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

theorem output_lt (n : Nat) : output n < 41125 :=
  Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
