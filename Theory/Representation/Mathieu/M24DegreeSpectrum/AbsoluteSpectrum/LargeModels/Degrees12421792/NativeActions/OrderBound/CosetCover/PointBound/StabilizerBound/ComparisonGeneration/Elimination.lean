module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.StabilizerBound.ComparisonGeneration.EliminationChecked

/-!
# Relative elimination for the eight fixed comparison words

The eight new letters denote exactly `Comparison.generatorWord`. Elementary
Tietze equations recover twenty original letters from those eight and original
letters 2, 7, 10, 17 (zero based). This is a relative generation reduction;
no membership of the four survivors is assumed by the replay itself.
Source: the literal ATLAS M24G1-P1 Schreier presentation. See `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison.Elimination
open Subgroup.CosetWordCertificate
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction

variable {G : Type*} [Group G] (g : Nat → G)
  (hi : ∀ r : Fin 445, eval g (inputWord r) = 1)
include hi

/-- The remaining subgroup-membership obligations are the four survivor letters. -/
theorem original_mem (H : Subgroup G)
    (hs : g 2 ∈ H ∧ g 7 ∈ H ∧ g 10 ∈ H ∧ g 17 ∈ H)
    (hc : ∀ a : Fin 8, g (24 + a.val) ∈ H) : ∀ a : Fin 24, g a.val ∈ H := by
  obtain ⟨mem3, mem8, mem11, mem18⟩ := hs
  have mem25 : g 24 ∈ H := hc 0
  have mem26 : g 25 ∈ H := hc 1
  have mem27 : g 26 ∈ H := hc 2
  have mem28 : g 27 ∈ H := hc 3
  have mem29 : g 28 ∈ H := hc 4
  have mem30 : g 29 ∈ H := hc 5
  have mem31 : g 30 ∈ H := hc 6
  have mem32 : g 31 ∈ H := hc 7
  have mem9 : g 8 ∈ H := by
    rw [eq9 g hi]
    simpa only [replacement9, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem3) (H.mul_mem (H.inv_mem mem11) (H.mul_mem (H.inv_mem mem8) (H.mul_mem mem11 (H.mul_mem mem29 (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem3) (H.mul_mem mem18 (H.mul_mem mem32 (H.mul_mem (H.inv_mem mem18) (H.mul_mem mem8 (H.mul_mem mem18 (H.mul_mem (H.inv_mem mem25) (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem11) (H.mul_mem (H.inv_mem mem3) (H.mul_mem (H.inv_mem mem3) (H.mul_mem (H.inv_mem mem11) (H.mul_mem (H.inv_mem mem8) (H.mul_mem mem11 (H.mul_mem mem29 (H.mul_mem (H.inv_mem mem25) (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem11) (H.mul_mem (H.inv_mem mem3) (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem3) (H.mul_mem mem8 (H.mul_mem (H.inv_mem mem25) (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem11) (H.mul_mem (H.inv_mem mem3) (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem3) (H.mul_mem mem8 (H.mul_mem (H.inv_mem mem29) (H.mul_mem (H.inv_mem mem11) (H.mul_mem mem8 (H.mul_mem mem11 (H.mul_mem mem3 (H.mul_mem mem8 (H.mul_mem (H.inv_mem mem25) (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem11) (H.mul_mem (H.inv_mem mem3) H.one_mem)))))))))))))))))))))))))))))))))))))))))))))
  have mem16 : g 15 ∈ H := by
    rw [eq16 g hi]
    simpa only [replacement16, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem11) (H.mul_mem mem3 (H.mul_mem mem8 (H.mul_mem mem3 (H.mul_mem mem11 (H.mul_mem mem8 (H.mul_mem mem25 (H.mul_mem (H.inv_mem mem29) (H.mul_mem (H.inv_mem mem11) (H.mul_mem mem8 (H.mul_mem mem11 (H.mul_mem mem3 H.one_mem))))))))))))
  have mem21 : g 20 ∈ H := by
    rw [eq21 g hi]
    simpa only [replacement21, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem mem8 (H.mul_mem (H.inv_mem mem29) (H.mul_mem (H.inv_mem mem11) (H.mul_mem mem8 (H.mul_mem mem11 (H.mul_mem mem3 (H.mul_mem mem8 (H.mul_mem (H.inv_mem mem18) H.one_mem))))))))
  have mem12 : g 11 ∈ H := by
    rw [eq12 g hi]
    simpa only [replacement12, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem16) (H.mul_mem (H.inv_mem mem11) (H.mul_mem mem21 (H.mul_mem mem18 (H.mul_mem (H.inv_mem mem25) (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem11) (H.mul_mem (H.inv_mem mem3) (H.mul_mem mem21 H.one_mem))))))))))
  have mem24 : g 23 ∈ H := by
    rw [eq24 g hi]
    simpa only [replacement24, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem mem3 (H.mul_mem mem18 (H.mul_mem (H.inv_mem mem32) (H.mul_mem (H.inv_mem mem18) (H.mul_mem mem11 (H.mul_mem mem16 (H.mul_mem mem18 (H.mul_mem mem12 H.one_mem))))))))
  have mem23 : g 22 ∈ H := by
    rw [eq23 g hi]
    simpa only [replacement23, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem mem24 (H.mul_mem (H.inv_mem mem12) (H.mul_mem (H.inv_mem mem18) (H.mul_mem (H.inv_mem mem3) (H.mul_mem (H.inv_mem mem11) (H.mul_mem (H.inv_mem mem9) (H.mul_mem mem16 (H.mul_mem mem9 H.one_mem))))))))
  have mem19 : g 18 ∈ H := by
    rw [eq19 g hi]
    simpa only [replacement19, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem8) (H.mul_mem mem18 (H.mul_mem (H.inv_mem mem32) (H.mul_mem (H.inv_mem mem18) H.one_mem))))
  have mem5 : g 4 ∈ H := by
    rw [eq5 g hi]
    simpa only [replacement5, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem25) (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem11) (H.mul_mem mem8 H.one_mem))))
  have mem15 : g 14 ∈ H := by
    rw [eq15 g hi]
    simpa only [replacement15, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem18) (H.mul_mem (H.inv_mem mem21) (H.mul_mem mem3 (H.mul_mem mem19 H.one_mem))))
  have mem20 : g 19 ∈ H := by
    rw [eq20 g hi]
    simpa only [replacement20, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem19) (H.mul_mem mem18 (H.mul_mem mem5 (H.mul_mem (H.inv_mem mem8) (H.mul_mem (H.inv_mem mem3) (H.mul_mem (H.inv_mem mem16) (H.mul_mem (H.inv_mem mem11) H.one_mem)))))))
  have mem14 : g 13 ∈ H := by
    rw [eq14 g hi]
    simpa only [replacement14, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem mem9 (H.mul_mem (H.inv_mem mem3) (H.mul_mem (H.inv_mem mem11) (H.mul_mem (H.inv_mem mem9) (H.mul_mem mem16 H.one_mem)))))
  have mem13 : g 12 ∈ H := by
    rw [eq13 g hi]
    simpa only [replacement13, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem29) (H.mul_mem (H.inv_mem mem11) (H.mul_mem mem8 (H.mul_mem mem11 H.one_mem))))
  have mem4 : g 3 ∈ H := by
    rw [eq4 g hi]
    simpa only [replacement4, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem mem24 (H.mul_mem (H.inv_mem mem12) (H.mul_mem (H.inv_mem mem18) (H.mul_mem (H.inv_mem mem23) H.one_mem))))
  have mem2 : g 1 ∈ H := by
    rw [eq2 g hi]
    simpa only [replacement2, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem21) (H.mul_mem (H.inv_mem mem19) (H.mul_mem (H.inv_mem mem26) (H.mul_mem (H.inv_mem mem15) H.one_mem))))
  have mem22 : g 21 ∈ H := by
    rw [eq22 g hi]
    simpa only [replacement22, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem15) (H.mul_mem (H.inv_mem mem23) H.one_mem))
  have mem10 : g 9 ∈ H := by
    rw [eq10 g hi]
    simpa only [replacement10, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem11) H.one_mem)
  have mem6 : g 5 ∈ H := by
    rw [eq6 g hi]
    simpa only [replacement6, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem5) H.one_mem)
  have mem17 : g 16 ∈ H := by
    rw [eq17 g hi]
    simpa only [replacement17, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem7 : g 6 ∈ H := by
    rw [eq7 g hi]
    simpa only [replacement7, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem1 : g 0 ∈ H := by
    rw [eq1 g hi]
    simpa only [replacement1, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  intro a
  fin_cases a
  · exact mem1
  · exact mem2
  · exact mem3
  · exact mem4
  · exact mem5
  · exact mem6
  · exact mem7
  · exact mem8
  · exact mem9
  · exact mem10
  · exact mem11
  · exact mem12
  · exact mem13
  · exact mem14
  · exact mem15
  · exact mem16
  · exact mem17
  · exact mem18
  · exact mem19
  · exact mem20
  · exact mem21
  · exact mem22
  · exact mem23
  · exact mem24

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison.Elimination
