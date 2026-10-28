module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.factCodesTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Generation.outputsTable

/-! Kernel-checked Schreier generation data. Reproduce with `source/Generate.py`.
Source: the six literal ATLAS relators and max3 words; see `source/README.md`. -/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
open Subgroup.CosetWordCertificate

def outputCheck (n : Nat) : Bool :=
  Scan.pathCheck facts 76703 0 (outputs n) 0 &&
    decide (reduce (Scan.pathWord facts (outputs n)) =
      [(⟨n % 367, Nat.mod_lt _ (by decide)⟩, true)])

def outputChunk (start count : Nat) : Bool :=
  (List.range count).all fun k => outputCheck (start + k)

theorem outputChunk_spec (start count : Nat) (hc : outputChunk start count = true)
    (k : Label) (hlo : start ≤ k.val) (hhi : k.val < start + count) :
    Scan.pathCheck facts 76703 0 (outputs k.val) 0 = true ∧
      reduce (Scan.pathWord facts (outputs k.val)) = [(k, true)] := by
  have hm : k.val - start ∈ List.range count := by simp only [List.mem_range]; omega
  have hh := List.all_eq_true.mp hc (k.val - start) hm
  have he : start + (k.val - start) = k.val := by omega
  simpa only [he, outputCheck, Bool.and_eq_true, decide_eq_true_eq,
    Nat.mod_eq_of_lt k.isLt, Fin.eta] using hh

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
