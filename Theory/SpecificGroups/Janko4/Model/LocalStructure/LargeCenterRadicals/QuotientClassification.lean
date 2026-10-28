module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Classification
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveRows.Classification
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.ResidualQuotients

/-!
# The selective large-center radical classification from the native cover

The two small-center locals are excluded by radical saturation. In max1 the
actual image is trivial or the full octad kernel, giving M₂₄ or A₈; in N(F)
the already proved exterior-square calculation gives SL₅(2) or A₈. Every
transport uses the full ambient normalizer and its full intrinsic two-core.
The original source-layer cover is supplied in the final CFSG assembly.

Source: An--O'Brien--Wilson (2003), §4 and Table 1, pp.122,124.
-/
public section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals

/-- The actual three quotient alternatives for an arbitrary large-center radical. -/
theorem radical_quotient_of_cover (hcover : MaximalTwoLocalCover)
    (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P)) :
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      Sporadic.Mathieu.M24) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8)) := by
  obtain ⟨g,hg | hg⟩ := large_center_normalizer_two_branches hcover P hP hlarge
  · exact Or.inr (MathieuRows.radical_quotient_of_conjugate P hP hlarge g hg)
  · rcases LinearFiveRows.radical_quotient_of_conjugate P hP hlarge g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end Janko4.LocalStructure.LargeCenterRadicals
