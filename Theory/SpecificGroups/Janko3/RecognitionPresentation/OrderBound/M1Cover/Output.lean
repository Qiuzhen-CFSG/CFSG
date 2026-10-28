module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.outputCode
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.destCode
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Facts
public import Theory.GroupTheory.CosetWordCertificateBoolean

/-! Kernel-checked coset certificate for ATLAS J3G1-P1, literal subgroup M₁.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

def output (n : Nat) : Nat := min (outputCode n) 277280

def destination (n : Nat) : Fin 6156 :=
  ⟨min (destCode n) 6155, by omega⟩

def shapeAt (n : Nat) : Bool :=
  factBEq (facts (output n)) ⟨n / 4, [decode (n % 4)], (destination n).val⟩

def shapeChunk (start count : Nat) : Bool :=
  (List.range count).all fun k => shapeAt (start+k)

theorem shapeChunk_sound {start count : Nat} (h : shapeChunk start count = true)
    (n : Nat) (hlo : start ≤ n) (hhi : n < start+count) : shapeAt n = true := by
  have hm : n-start ∈ List.range count := by simp only [List.mem_range]; omega
  have hs := List.all_eq_true.mp h (n-start) hm
  have he : start + (n-start) = n := by omega
  rwa [he] at hs

theorem output_lt (n : Nat) : output n < 277281 :=
  Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
