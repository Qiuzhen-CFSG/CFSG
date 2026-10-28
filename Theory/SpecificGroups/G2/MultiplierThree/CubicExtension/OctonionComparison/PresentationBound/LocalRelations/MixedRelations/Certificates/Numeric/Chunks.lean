module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Data
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Checker
/-! Bounded numeric checks and their interval assembly for the pinned cyclic trace. -/
@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric
def checkChunk (start count : Nat) : Bool :=
  (List.range count).all fun k =>
    packedCheck definitionCode factCode instructionCode (start + k)

def Checked (start stop : Nat) : Prop :=
  ∀ n, start ≤ n → n < stop →
    Pooled.check (pool (fun _ => [])) definitionCode facts n (instructions n) (facts n) = true

theorem checkChunk_sound (start count : Nat) (h : checkChunk start count = true) :
    Checked start (start + count) := by
  intro n hlo hhi
  have hm : n - start ∈ List.range count := by simp only [List.mem_range]; omega
  have hn : start + (n - start) = n := by omega
  have hc := List.all_eq_true.mp h (n - start) hm
  change packedCheck definitionCode factCode instructionCode (start + (n - start)) = true at hc
  rw [hn] at hc
  exact packedCheck_sound _ _ _ _ hc

theorem Checked.append {a b c : Nat} (h₁ : Checked a b) (h₂ : Checked b c) : Checked a c := by
  intro n hlo hhi
  by_cases h : n < b
  · exact h₁ n hlo h
  · exact h₂ n (by omega) hhi

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric
