module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.ReducedPresentation

/-!
# Checked reduction of the natural-point Schreier presentation

All 19 reduced relations hold on the marked pair, and the recorded generator
equations recover every original generator. Thus the map from the reduced
presentation onto the original presentation is surjective. The finite bound
is explicitly left to the smaller presentation; this module does not assert it.
Source: ATLAS M24G1-P1 and the checked replay in `source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound
open Subgroup.CosetWordCertificate Reduction

section Replay
variable {G : Type*} [Group G] (g : Nat → G)
  (hi : ∀ r, eval g (inputWord r) = 1)
include hi

theorem reduced_relations : ∀ r,
    eval (fun a : Fin 2 => g (survivor a).val) (reducedRelatorLetters r) = 1 := by
  intro r
  refine (eval_map_letters g (fun a : Fin 2 => (survivor a).val)
    (reducedRelatorLetters r)).symm.trans ?_
  fin_cases r
  · exact h413 g hi
  · exact h34 g hi
  · exact h497 g hi
  · exact h614 g hi
  · exact h624 g hi
  · exact h660 g hi
  · exact h663 g hi
  · exact h674 g hi
  · exact h683 g hi
  · exact h684 g hi
  · exact h688 g hi
  · exact h689 g hi
  · exact h692 g hi
  · exact h694 g hi
  · exact h695 g hi
  · exact h697 g hi
  · exact h698 g hi
  · exact h700 g hi
  · exact h704 g hi

/-- Recovery takes place in ordinary subgroup closure, with no normality assumption. -/
theorem generators_mem (H : Subgroup G)
    (hs : ∀ a : Fin 2, g (survivor a).val ∈ H) : ∀ a : Fin 25, g a.val ∈ H := by
  have mem21 : g 20 ∈ H := hs 0
  have mem25 : g 24 ∈ H := hs 1
  have mem2 : g 1 ∈ H := by
    rw [eq2 g hi]
    simpa only [replacement2, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem21) (H.mul_mem (H.inv_mem mem25) (H.mul_mem (H.inv_mem mem25) (H.mul_mem (H.inv_mem mem25) (H.mul_mem mem21 (H.mul_mem mem25 (H.mul_mem mem25 (H.mul_mem mem25 (H.mul_mem mem21 H.one_mem)))))))))
  have mem6 : g 5 ∈ H := by
    rw [eq6 g hi]
    simpa only [replacement6, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem mem21 (H.mul_mem mem2 (H.mul_mem (H.inv_mem mem21) (H.mul_mem mem2 (H.mul_mem mem21 (H.mul_mem mem25 (H.mul_mem mem25 (H.mul_mem mem21 (H.mul_mem mem2 H.one_mem)))))))))
  have mem19 : g 18 ∈ H := by
    rw [eq19 g hi]
    simpa only [replacement19, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem6) (H.mul_mem mem2 (H.mul_mem mem6 (H.mul_mem (H.inv_mem mem2) (H.mul_mem mem6 H.one_mem)))))
  have mem17 : g 16 ∈ H := by
    rw [eq17 g hi]
    simpa only [replacement17, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem mem25 (H.mul_mem mem25 (H.mul_mem mem21 (H.mul_mem mem2 H.one_mem))))
  have mem9 : g 8 ∈ H := by
    rw [eq9 g hi]
    simpa only [replacement9, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem mem21 (H.mul_mem mem2 (H.mul_mem (H.inv_mem mem21) H.one_mem)))
  have mem23 : g 22 ∈ H := by
    rw [eq23 g hi]
    simpa only [replacement23, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using (H.mul_mem (H.inv_mem mem25) H.one_mem)
  have mem24 : g 23 ∈ H := by
    rw [eq24 g hi]
    simpa only [replacement24, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem22 : g 21 ∈ H := by
    rw [eq22 g hi]
    simpa only [replacement22, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem20 : g 19 ∈ H := by
    rw [eq20 g hi]
    simpa only [replacement20, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem18 : g 17 ∈ H := by
    rw [eq18 g hi]
    simpa only [replacement18, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem16 : g 15 ∈ H := by
    rw [eq16 g hi]
    simpa only [replacement16, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem15 : g 14 ∈ H := by
    rw [eq15 g hi]
    simpa only [replacement15, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem14 : g 13 ∈ H := by
    rw [eq14 g hi]
    simpa only [replacement14, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem13 : g 12 ∈ H := by
    rw [eq13 g hi]
    simpa only [replacement13, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem12 : g 11 ∈ H := by
    rw [eq12 g hi]
    simpa only [replacement12, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem11 : g 10 ∈ H := by
    rw [eq11 g hi]
    simpa only [replacement11, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem10 : g 9 ∈ H := by
    rw [eq10 g hi]
    simpa only [replacement10, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem8 : g 7 ∈ H := by
    rw [eq8 g hi]
    simpa only [replacement8, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem7 : g 6 ∈ H := by
    rw [eq7 g hi]
    simpa only [replacement7, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem5 : g 4 ∈ H := by
    rw [eq5 g hi]
    simpa only [replacement5, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem4 : g 3 ∈ H := by
    rw [eq4 g hi]
    simpa only [replacement4, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
  have mem3 : g 2 ∈ H := by
    rw [eq3 g hi]
    simpa only [replacement3, eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte] using H.one_mem
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
  · exact mem25

end Replay

/-- The canonical generators, extended to the natural-number certificate alphabet. -/
def certificateGenerator (n : Nat) : Presented :=
  PresentedGroup.of ⟨n % 25, Nat.mod_lt _ (by decide)⟩

@[simp] theorem certificateGenerator_fin (i : Fin 25) :
    certificateGenerator i.val = PresentedGroup.of i := by
  simp only [certificateGenerator, Nat.mod_eq_of_lt i.isLt, Fin.eta]

private theorem generator_relations (r : Fin 24 × Fin 7) :
    eval (PresentedGroup.of : Fin 25 → Presented) (relatorLetters r) = 1 := by
  have hm : FreeGroup.lift (PresentedGroup.of : Fin 25 → Presented) =
      PresentedGroup.mk (Set.range relator) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  change FreeGroup.lift (PresentedGroup.of : Fin 25 → Presented) (relator r) = 1
  rw [hm]
  exact PresentedGroup.one_of_mem ⟨r, rfl⟩

theorem input_relations (r : Fin 168) : eval certificateGenerator (inputWord r) = 1 := by
  rw [inputWord, eval_map_letters]
  simpa only [Function.comp_def, certificateGenerator_fin] using
    generator_relations (⟨r.val / 7, by omega⟩, ⟨r.val % 7, by omega⟩)

/-- Marked epimorphism, taking the reduced pair to original generators 20 and 24. -/
def toPresented : ReducedPresented →* Presented :=
  PresentedGroup.toGroup (f := fun a => PresentedGroup.of (survivor a)) (by
    rintro _ ⟨r, rfl⟩
    simpa only [certificateGenerator_fin, eval, reducedRelator] using
      reduced_relations certificateGenerator input_relations r)

@[simp] theorem toPresented_generator (a : Fin 2) :
    toPresented (PresentedGroup.of a) = PresentedGroup.of (survivor a) :=
  PresentedGroup.toGroup.of _

theorem toPresented_surjective : Function.Surjective toPresented := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← PresentedGroup.closure_range_of (Set.range relator)]
  apply (Subgroup.closure_le toPresented.range).mpr
  rintro _ ⟨a, rfl⟩
  have hm := generators_mem certificateGenerator input_relations toPresented.range
    (fun b => by
      rw [certificateGenerator_fin]
      exact ⟨PresentedGroup.of b, toPresented_generator b⟩) a
  simpa only [certificateGenerator_fin, SetLike.mem_coe] using hm

/-- This discharges the original presentation bound once the smaller bound is proved. -/
theorem presented_bound_of_reduced_bound
    (h : Finite ReducedPresented ∧ Nat.card ReducedPresented ≤ 10200960) :
    Finite Presented ∧ Nat.card Presented ≤ 10200960 := by
  let : Finite ReducedPresented := h.1
  exact ⟨Finite.of_surjective _ toPresented_surjective,
    (Nat.card_le_card_of_surjective _ toPresented_surjective).trans h.2⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound
