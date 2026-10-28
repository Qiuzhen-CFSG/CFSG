module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorCodesTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.relatorDataTable

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

def relations (n : Nat) : Word Label :=
  if n < 3113 then relatorData n else []

def sourceCheck (n : Nat) : Bool := decide (relator (relatorCodes n) = relations n)

def sourceChunk (start count : Nat) : Bool :=
  (List.range count).all fun k => sourceCheck (start + k)

theorem sourceChunk_eq (start count : Nat) (hc : sourceChunk start count = true)
    (n : Nat) (hlo : start ≤ n) (hhi : n < start + count) :
    relator (relatorCodes n) = relations n := by
  have hm : n - start ∈ List.range count := by simp only [List.mem_range]; omega
  have hh := List.all_eq_true.mp hc (n - start) hm
  have he : start + (n - start) = n := by omega
  simpa only [he, sourceCheck, decide_eq_true_eq] using hh

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
