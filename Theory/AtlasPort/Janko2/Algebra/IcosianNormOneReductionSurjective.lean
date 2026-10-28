/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormOneReductionSurjective.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneKernelCard
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneCard
public import Theory.AtlasPort.Janko2.Algebra.GoldenFourFinite
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# IcosianNormOneReductionSurjective

Every matrix in SL₂(F₄) lifts to an integral norm-one quaternion.
The source group has 120 elements and the kernel has two, so the image
has the full SL₂(F₄) order 60.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormOneReductionSurjective.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped MatrixGroups

theorem goldenFour_SL_card : Nat.card (Matrix.SpecialLinearGroup (Fin 2) GoldenFour)=60 := by
  have hc : Nat.card GoldenFour=4 := by rw [Nat.card_eq_fintype_card,goldenFour_card]
  rw [Atlas.card_sl_two, hc]
  norm_num

/-- Every determinant-one matrix lifts to an actual integral norm-one quaternion. -/
theorem icosianNormOneReduction_surjective : Function.Surjective icosianNormOneReduction := by
  have h := icosianNormOneReduction.ker.card_eq_card_quotient_mul_card_subgroup
  rw [icosianNormOneGroup_card,icosianNormOneReduction_kernel_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange icosianNormOneReduction).toEquiv] at h
  have hr : Nat.card icosianNormOneReduction.range=60 := by omega
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [hr,goldenFour_SL_card]

end Atlas.Algebra
