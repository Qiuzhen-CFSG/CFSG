/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormOneKernel.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneReduction
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoKernel
public import Theory.AtlasPort.Janko2.Algebra.IcosianWeightedNorm

/-!
# IcosianNormOneKernel

A norm-one integral icosian congruent to one modulo two is a sign.
Writing it as 1 + 2y and using the positive integral weighted norm
forces y to be zero or minus one.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormOneKernel.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

theorem icosian_normOne_congr_one (x : icosianOrder) (hn : icosianNorm x.val=1)
    (hx : icosianModuloTwo x=1) : x.val=1 ∨ x.val= -1 := by
  have hz : icosianModuloTwo (x-1)=0 := by rw [map_sub,hx,map_one,sub_self]
  obtain ⟨y,hy⟩ := (icosianModuloTwo_eq_zero_iff_two_mul _).mp hz
  have he : x.val=1+2*y.val := by
    have hh := congrArg Subtype.val hy
    change x.val-1=2*y.val at hh
    rw [sub_eq_iff_eq_add] at hh
    exact hh.trans (add_comm _ _)
  have hnorm := icosianNorm_one_add_two y.val
  rw [← he,hn] at hnorm
  have hf := congrArg goldenFunctional hnorm
  have hlin : goldenFunctional y.val.re= -icosianWeightedNorm y.val := by
    simp [goldenFunctional,icosianWeightedNorm] at hf ⊢
    linarith
  let n : ℤ := (icosianIntegralNorm y).re
  have hval : icosianWeightedNorm y.val=(n : ℚ) := icosianWeightedNorm_integral y
  have hnonneg : 0≤n := by
    have h := icosianWeightedNorm_nonneg y.val
    rw [hval] at h
    exact_mod_cast h
  have hbound : n^2≤n := by
    have h := icosianWeightedNorm_real_bound y.val
    rw [hlin,hval] at h
    exact_mod_cast (show (n : ℚ)^2≤(n : ℚ) by nlinarith)
  have hc : n=0 ∨ n=1 := by
    have hle : n≤1 := by nlinarith
    omega
  rcases hc with hc | hc
  · left
    have hy0 : y.val=0 := (icosianWeightedNorm_eq_zero _).mp (by rw [hval,hc]; norm_num)
    simpa [hy0] using he
  · right
    have hy0 : y.val+1=0 := (icosianWeightedNorm_eq_zero _).mp (by
      rw [icosianWeightedNorm_add_one,hlin,hval,hc]
      norm_num)
    have hy1 : y.val= -1 := eq_neg_of_add_eq_zero_left hy0
    rw [he,hy1]
    noncomm_ring

theorem icosianNormOneReduction_kernel_values (u : icosianNormOneGroup)
    (h : icosianNormOneReduction u=1) : u.val.val=1 ∨ u.val.val= -1 := by
  apply icosian_normOne_congr_one (icosianNormOneToOrder u) (icosianNormOneGroup_norm u)
  exact congrArg Subtype.val h

end Atlas.Algebra
