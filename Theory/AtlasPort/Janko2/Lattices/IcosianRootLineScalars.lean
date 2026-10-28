/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootLineScalars.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRootNormShapes
public import Theory.AtlasPort.Janko2.Lattices.IcosianRoots
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormTwoAssociates
public import Theory.AtlasPort.Janko2.Algebra.IcosianDivision

/-!
# Icosian Root Line Scalars

A quaternionic scalar relating two actual roots is an integral norm-one
icosian. The root norm gives norm one; the exhaustive coordinate shapes
and the row-ideal arithmetic recover integrality.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootLineScalars.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped Quaternion Matrix BigOperators

/-- Scalar relating two actual norm-two roots has reduced norm one. -/
theorem icosianRoot_scalar_norm (r s : IcosianRoot) (a : IcosianQuaternion)
    (h : ∀ i,(s.val i).val=(r.val i).val*a) : icosianNorm a=1 := by
  have hr : (∑ i,icosianNorm (r.val i).val)=4 := by
    have q := congrArg goldenIntegerToRational
      (icosianRoot_integral_norm_sum r.val r.property.2)
    simpa only [map_sum,icosianIntegralNorm_spec,map_ofNat] using q
  have hs : (∑ i,icosianNorm (s.val i).val)=4 := by
    have q := congrArg goldenIntegerToRational
      (icosianRoot_integral_norm_sum s.val s.property.2)
    simpa only [map_sum,icosianIntegralNorm_spec,map_ofNat] using q
  simp_rw [h,icosianNorm_mul] at hs
  rw [← Finset.sum_mul,hr] at hs
  apply mul_left_cancel₀ (show (4 : GoldenRational)≠0 by norm_num)
  simpa using hs

theorem icosianRoot_scalar_coordinate_norm (r s : IcosianRoot) (a : IcosianQuaternion)
    (h : ∀ i,(s.val i).val=(r.val i).val*a) (i : Fin 3) :
    icosianNorm (s.val i).val=icosianNorm (r.val i).val := by
  rw [h,icosianNorm_mul,icosianRoot_scalar_norm r s a h,mul_one]

/-- An integral coordinate of norm one recovers the scalar integrally. -/
theorem icosianRoot_scalar_integral_of_one (r s : IcosianRoot) (a : IcosianQuaternion)
    (h : ∀ i,(s.val i).val=(r.val i).val*a) (i : Fin 3)
    (hi : icosianNorm (r.val i).val=1) : IsIcosian a := by
  have he : star (r.val i).val*(s.val i).val=a := by
    rw [h,← mul_assoc,Quaternion.star_mul_self]
    change (icosianNorm (r.val i).val : IcosianQuaternion)*a=a
    rw [hi]
    simp
  rw [← he]
  exact icosianOrder.mul_mem (icosianOrder_star_mem (r.val i).property) (s.val i).property

/-- Within the common row ideal, norm-two coordinates determine an integral unit scalar. -/
theorem icosianRoot_scalar_integral_of_two (r s : IcosianRoot) (a : IcosianQuaternion)
    (h : ∀ i,(s.val i).val=(r.val i).val*a) (i j : Fin 3)
    (hi : icosianNorm (r.val i).val=2) (hj : r.val j=0) : IsIcosian a := by
  have hsj : s.val j=0 := by
    apply Subtype.ext
    rw [h,hj]
    simp
  have hsi : icosianNorm (s.val i).val=2 :=
    (icosianRoot_scalar_coordinate_norm r s a h i).trans hi
  have hr0 := icosianLeechModule_zero_row r.val r.property.1 j hj i
  have hs0 := icosianLeechModule_zero_row s.val s.property.1 j hsj i
  have hz : Matrix.adjugate (icosianModuloTwo (r.val i))*icosianModuloTwo (s.val i)=0 := by
    funext k l
    fin_cases k <;> fin_cases l <;>
      simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hr0,hs0]
  obtain ⟨u,hu⟩ := icosianNormTwo_associate_of_adjugate hi hsi hz
  have hn : (r.val i).val≠0 := by intro hh; rw [hh] at hi; norm_num [icosianNorm] at hi
  have he : a=u.val.val := mul_left_cancel₀ hn ((h i).symm.trans hu)
  rw [he]
  exact u.property

/-- A coordinate-axis root is twice an integral norm-one scalar. -/
theorem icosianRoot_scalar_integral_of_axis (r s : IcosianRoot) (a : IcosianQuaternion)
    (h : ∀ i,(s.val i).val=(r.val i).val*a) (i : Fin 3)
    (hz : ∀ j,j≠i → r.val j=0) : IsIcosian a := by
  have hsz : ∀ j,j≠i → s.val j=0 := by
    intro j hj
    apply Subtype.ext
    rw [h,hz j hj]
    simp
  have hrx : icosianSingle i (r.val i)=r.val := by
    funext j
    by_cases hj : j=i
    · subst j; simp [icosianSingle]
    · simp [icosianSingle,hj,hz j hj]
  have hsx : icosianSingle i (s.val i)=s.val := by
    funext j
    by_cases hj : j=i
    · subst j; simp [icosianSingle]
    · simp [icosianSingle,hj,hsz j hj]
  have hr0 := (icosianSingle_mem i (r.val i)).mp (hrx.symm ▸ r.property.1)
  have hs0 := (icosianSingle_mem i (s.val i)).mp (hsx.symm ▸ s.property.1)
  obtain ⟨v,hv⟩ := (icosianModuloTwo_eq_zero_iff_two_mul _).mp hr0
  obtain ⟨w,hw⟩ := (icosianModuloTwo_eq_zero_iff_two_mul _).mp hs0
  have hvq : (r.val i).val=2*v.val := congrArg Subtype.val hv
  have hwq : (s.val i).val=2*w.val := congrArg Subtype.val hw
  have hvn : icosianNorm v.val=1 := by
    have hn := icosianRoot_single_norm r i hz
    rw [hvq,icosianNorm_double] at hn
    apply mul_left_cancel₀ (show (4 : GoldenRational)≠0 by norm_num)
    simpa using hn
  have hva : v.val*a=w.val := by
    have hh := h i
    rw [hvq,hwq,mul_assoc] at hh
    exact (mul_left_cancel₀ (show (2 : IcosianQuaternion)≠0 by intro he; have hh := congrArg (fun z : IcosianQuaternion => z.re.re) he; norm_num [QuaternionAlgebra.re_ofNat, QuadraticAlgebra.re_ofNat] at hh) hh).symm
  have ha : a=star v.val*w.val := by
    rw [← hva,← mul_assoc,Quaternion.star_mul_self]
    change a=(icosianNorm v.val : IcosianQuaternion)*a
    rw [hvn]
    simp
  rw [ha]
  exact icosianOrder.mul_mem (icosianOrder_star_mem v.property) w.property

/-- The scalar on a quaternionic line through actual roots is an actual integral unit. -/
theorem icosianRoot_scalar_integral (r s : IcosianRoot) (a : IcosianQuaternion)
    (h : ∀ i,(s.val i).val=(r.val i).val*a) : IsIcosian a := by
  let n := fun i => icosianIntegralNorm (r.val i)
  have hm (t : GoldenInteger) (ht : t∈[n 0,n 1,n 2]) : ∃ i,n i=t := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at ht
    rcases ht with ht | ht | ht
    · exact ⟨0,ht.symm⟩
    · exact ⟨1,ht.symm⟩
    · exact ⟨2,ht.symm⟩
  have hval (i : Fin 3) : goldenIntegerToRational (n i)=icosianNorm (r.val i).val :=
    icosianIntegralNorm_spec _
  rcases icosianRoot_norm_shapes r.val r.property.1 r.property.2 with hA | hB | hC | hD
  · obtain ⟨i,hi⟩ := hm 4 (hA.mem_iff.mpr (by simp))
    have hsum := congrArg QuadraticAlgebra.re (icosianRoot_integral_norm_sum r.val r.property.2)
    have h0 := icosianIntegralNorm_real_nonneg (r.val 0)
    have h1 := icosianIntegralNorm_real_nonneg (r.val 1)
    have h2 := icosianIntegralNorm_real_nonneg (r.val 2)
    have hir : (n i).re=4 := by rw [hi]; rfl
    have hz : ∀ j,j≠i → r.val j=0 := by
      intro j hj
      apply (icosianIntegralNorm_real_zero _).mp
      simp [Fin.sum_univ_succ,QuadraticAlgebra.re_ofNat] at hsum
      fin_cases i <;> fin_cases j <;> simp_all [n] <;> omega
    exact icosianRoot_scalar_integral_of_axis r s a h i hz
  · obtain ⟨i,hi⟩ := hm 2 (hB.mem_iff.mpr (by simp))
    obtain ⟨j,hj⟩ := hm 0 (hB.mem_iff.mpr (by simp))
    apply icosianRoot_scalar_integral_of_two r s a h i j
    · rw [← hval,hi]; rfl
    · apply (icosianIntegralNorm_real_zero _).mp
      change (n j).re=0
      rw [hj]; rfl
  · obtain ⟨i,hi⟩ := hm 1 (hC.mem_iff.mpr (by simp))
    apply icosianRoot_scalar_integral_of_one r s a h i
    rw [← hval,hi]; rfl
  · obtain ⟨i,hi⟩ := hm 1 (hD.mem_iff.mpr (by simp))
    apply icosianRoot_scalar_integral_of_one r s a h i
    rw [← hval,hi]; rfl

theorem icosianRoot_scalar_unit (r s : IcosianRoot) (a : IcosianQuaternion)
    (h : ∀ i,(s.val i).val=(r.val i).val*a) :
    ∃ u : icosianNormOneGroup,a=u.val.val :=
  ⟨icosianNormOneGroupOf a (icosianRoot_scalar_integral r s a h)
    (icosianRoot_scalar_norm r s a h),rfl⟩

end Atlas.Lattices
