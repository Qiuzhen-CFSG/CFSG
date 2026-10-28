module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Hyperplanes.Bases
import Mathlib.Tactic.FinCases

/-!
# Fixed spaces of every hyperplane of the degree-eight disjoint-swap group

Every hyperplane is the kernel of one of the fifteen nonzero binary forms on
the swap coordinates. Counting fixed vectors, and normalized representatives
with constant displacement for the quotient modules, gives the four fixed
space dimensions. Only forms supported on one coordinate have the extra
full/deleted fixed dimension. The core and natural dimensions are always four
and three, including for the even part, whose form has support four.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(5),(6), printed pp. 83–84.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight
open Representation.BinaryOffender

set_option maxRecDepth 4096 in
private theorem dimensions_mask_1 : HasDimensions (hyperplaneKernel 1) 5 4 4 3 := by
  rw [hyperplaneKernel_closure_basis 1 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_2 : HasDimensions (hyperplaneKernel 2) 5 4 4 3 := by
  rw [hyperplaneKernel_closure_basis 2 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_3 : HasDimensions (hyperplaneKernel 3) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 3 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_4 : HasDimensions (hyperplaneKernel 4) 5 4 4 3 := by
  rw [hyperplaneKernel_closure_basis 4 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_5 : HasDimensions (hyperplaneKernel 5) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 5 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_6 : HasDimensions (hyperplaneKernel 6) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 6 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_7 : HasDimensions (hyperplaneKernel 7) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 7 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_8 : HasDimensions (hyperplaneKernel 8) 5 4 4 3 := by
  rw [hyperplaneKernel_closure_basis 8 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_9 : HasDimensions (hyperplaneKernel 9) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 9 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_10 : HasDimensions (hyperplaneKernel 10) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 10 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_11 : HasDimensions (hyperplaneKernel 11) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 11 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_12 : HasDimensions (hyperplaneKernel 12) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 12 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_13 : HasDimensions (hyperplaneKernel 13) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 13 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_14 : HasDimensions (hyperplaneKernel 14) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 14 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

set_option maxRecDepth 4096 in
private theorem dimensions_mask_15 : HasDimensions (hyperplaneKernel 15) 4 3 4 3 := by
  rw [hyperplaneKernel_closure_basis 15 (by decide)]
  apply dimensions
  all_goals rw [count_bits]; decide +kernel

/-- Fixed dimensions for every nonzero form: only support one leaves a pair
pointwise fixed. Quotient counts use constant displacement, not pointwise fixing. -/
theorem finrank_fixedSpace_hyperplaneKernel (m : Fin 16) (hm : m ≠ 0) :
    HasDimensions (hyperplaneKernel m)
      (if hyperplaneWeight m = 1 then 5 else 4)
      (if hyperplaneWeight m = 1 then 4 else 3) 4 3 := by
  fin_cases m
  · exact (hm rfl).elim
  · exact dimensions_mask_1
  · exact dimensions_mask_2
  · exact dimensions_mask_3
  · exact dimensions_mask_4
  · exact dimensions_mask_5
  · exact dimensions_mask_6
  · exact dimensions_mask_7
  · exact dimensions_mask_8
  · exact dimensions_mask_9
  · exact dimensions_mask_10
  · exact dimensions_mask_11
  · exact dimensions_mask_12
  · exact dimensions_mask_13
  · exact dimensions_mask_14
  · exact dimensions_mask_15

/-- Every hyperplane has rank three. -/
theorem rank_hyperplane {H : Subgroup Perm} (hH : H ⋖ D 8) : rank H = 3 := by
  obtain ⟨m, hm, rfl⟩ := hyperplane_eq_kernel hH
  exact rank_hyperplaneKernel m hm

theorem isElementaryTwo_hyperplane {H : Subgroup Perm} (hH : H ⋖ D 8) :
    IsElementaryTwo H := by
  obtain ⟨m, hm, rfl⟩ := hyperplane_eq_kernel hH
  exact isElementaryTwo_hyperplaneKernel m hm

/-- The fixed core and natural spaces have dimensions four and three for every
hyperplane, including the even part. -/
theorem finrank_fixedSpace_hyperplane {H : Subgroup Perm} (hH : H ⋖ D 8) :
    Module.finrank F (fixedSpace (BinaryPermutation.coreRepresentation (Fin 8)) H) = 4 ∧
    Module.finrank F (fixedSpace (BinaryPermutation.naturalRepresentation (Fin 8)) H) = 3 := by
  obtain ⟨m, hm, rfl⟩ := hyperplane_eq_kernel hH
  exact (finrank_fixedSpace_hyperplaneKernel m hm).2.2

/-- Both the core and natural fixed spaces have codimension three. -/
theorem fixedCodim_hyperplane {H : Subgroup Perm} (hH : H ⋖ D 8) :
    fixedCodim (BinaryPermutation.coreRepresentation (Fin 8)) H = 3 ∧
    fixedCodim (BinaryPermutation.naturalRepresentation (Fin 8)) H = 3 := by
  obtain ⟨m, hm, rfl⟩ := hyperplane_eq_kernel hH
  exact (codimensions _ _ _ _ _ (finrank_fixedSpace_hyperplaneKernel m hm)).2.2

/-- Four fixed dimensions of the even part, in order full, deleted, core, natural. -/
theorem finrank_fixedSpace_evenPart : HasDimensions (evenPart 8) 4 3 4 3 := by
  rw [evenPart_eq_hyperplaneKernel]
  simpa only [hyperplaneWeight_evenPart, show ¬ (4 : ℕ) = 1 by decide, if_false] using
    finrank_fixedSpace_hyperplaneKernel 15 (by decide)

/-- Four fixed codimensions of the even part. -/
theorem fixedCodim_evenPart :
    fixedCodim (BinaryPermutation.representation (Fin 8)) (evenPart 8) = 4 ∧
    fixedCodim (BinaryPermutation.deletedRepresentation (Fin 8)) (evenPart 8) = 4 ∧
    fixedCodim (BinaryPermutation.coreRepresentation (Fin 8)) (evenPart 8) = 3 ∧
    fixedCodim (BinaryPermutation.naturalRepresentation (Fin 8)) (evenPart 8) = 3 :=
  codimensions _ 4 3 4 3 finrank_fixedSpace_evenPart

end CFSG.Quasithin.ChapterB.Offenders.Eight
