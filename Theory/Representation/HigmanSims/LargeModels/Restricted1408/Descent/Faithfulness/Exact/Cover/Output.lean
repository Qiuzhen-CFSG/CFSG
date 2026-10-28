module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.outputCode
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.destCode
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Facts
public import Theory.GroupTheory.CosetWordCertificateBoolean

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

def output (n : Nat) : Nat := min (outputCode n) 331988

def destination (n : Nat) : Fin 5775 :=
  ⟨min (destCode n) 5774, by omega⟩

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

theorem output_lt (n : Nat) : output n < 331989 :=
  Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
