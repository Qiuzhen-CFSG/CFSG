module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.StabilizerBound.ComparisonGeneration.Elimination
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.StabilizerBound

/-!
# Applying relative elimination to the literal comparison subgroup

The certificate reads all used relations from `Stabilizer.relatorLetters`.
Its additional eight equations are definitions of the unchanged comparison
words. Four explicit subgroup memberships suffice for generation and hence,
independently of relation lifting, discharge the generation input of the
surjectivity theorem. See `source/README.md` for the source and conventions.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison
open Subgroup.CosetWordCertificate

namespace Elimination

/-- Interpret the old letters and the eight newly named words in the actual group. -/
def marked (n : Nat) : Presented :=
  if h : n < 24 then PresentedGroup.of ⟨n, h⟩
  else generator ⟨(n - 24) % 8, Nat.mod_lt _ (by decide)⟩

theorem marked_original (a : Fin 24) : marked a.val = PresentedGroup.of a := by
  simp only [marked, a.isLt, ↓reduceDIte]

theorem marked_comparison (a : Fin 8) : marked (24 + a.val) = generator a := by
  have hn : ¬24 + a.val < 24 := by omega
  simp only [marked, dif_neg hn]
  congr 1
  apply Fin.ext
  simp only [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt a.isLt]

theorem eval_original (w : Word (Fin 24)) :
    eval marked (w.map (fun a => (a.1.val, a.2))) = eval PresentedGroup.of w := by
  rw [eval_map_letters]
  congr 1
  funext a
  exact marked_original a

/-- Every certificate input follows from an original relation or a word definition. -/
theorem input_relations (r : Fin 445) : eval marked (inputWord r) = 1 := by
  unfold inputWord
  split
  · rw [eval_original]
    exact defining_relation _
  · rename_i hr
    rw [eval_append, eval_letter, eval_original]
    change (marked (r.val - 437 + 24))⁻¹ * generator ⟨r.val - 437, by omega⟩ = 1
    have hm : marked (r.val - 437 + 24) = generator ⟨r.val - 437, by omega⟩ := by
      simpa only [Nat.add_comm] using marked_comparison ⟨r.val - 437, by omega⟩
    rw [hm]
    exact inv_mul_cancel _

end Elimination

/-- A checked reduction of generation to four original subgroup memberships. -/
theorem generation_of_four
    (h2 : (PresentedGroup.of (2 : Fin 24) : Presented) ∈ subgroup)
    (h7 : (PresentedGroup.of (7 : Fin 24) : Presented) ∈ subgroup)
    (h10 : (PresentedGroup.of (10 : Fin 24) : Presented) ∈ subgroup)
    (h17 : (PresentedGroup.of (17 : Fin 24) : Presented) ∈ subgroup) : Generation := by
  have hs : Elimination.marked 2 ∈ subgroup ∧ Elimination.marked 7 ∈ subgroup ∧
      Elimination.marked 10 ∈ subgroup ∧ Elimination.marked 17 ∈ subgroup :=
    ⟨h2, h7, h10, h17⟩
  have hc : ∀ a : Fin 8, Elimination.marked (24 + a.val) ∈ subgroup := by
    intro a
    rw [Elimination.marked_comparison]
    exact Subgroup.subset_closure (Set.mem_range_self a)
  have hm := Elimination.original_mem Elimination.marked Elimination.input_relations
    subgroup hs hc
  apply top_unique
  rw [← PresentedGroup.closure_range_of (Set.range relator)]
  apply (Subgroup.closure_le subgroup).mpr
  rintro _ ⟨a, rfl⟩
  change (PresentedGroup.of a : Presented) ∈ subgroup
  have ha := hm a
  rw [Elimination.marked_original] at ha
  exact ha

/-- The actual consumer retains relation lifting as its independent premise. -/
theorem toPresented_surjective_of_four (hr : Relations)
    (h2 : (PresentedGroup.of (2 : Fin 24) : Presented) ∈ subgroup)
    (h7 : (PresentedGroup.of (7 : Fin 24) : Presented) ∈ subgroup)
    (h10 : (PresentedGroup.of (10 : Fin 24) : Presented) ∈ subgroup)
    (h17 : (PresentedGroup.of (17 : Fin 24) : Presented) ∈ subgroup) :
    Function.Surjective (toPresented hr) :=
  toPresented_surjective hr (generation_of_four h2 h7 h10 h17)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison
