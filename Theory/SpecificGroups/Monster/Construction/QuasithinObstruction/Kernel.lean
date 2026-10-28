module

public import Theory.SpecificGroups.Monster.Construction.QuasithinObstruction.Projection
public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Forms

/-!
# The two-group kernel of the actual Monster local quotient

An element above the scalar Leech signs acts trivially on the binary Leech
space. Compatibility and the two-element center of the extraspecial group
then make its induced automorphism square to one. A spin isometry inducing
the identity automorphism commutes with the spanning spin operators, hence
is scalar; positivity of the preserved real form makes its square one.
Thus every element in the pullback quotient kernel has fourth power one.
Surjectivity of the tensor-image map transfers this to C and the literal
embedded local subgroup, proving that both quotient kernels are two-groups.
No finiteness or simplicity of the ambient Griess carrier is assumed.

This is the kernel consequence of Aschbacher, *Sporadic Groups*, 27.6(1--2),
using the actual fiber product from 27.5 and its embedding from 28.12--28.13.
It supplies the coprime-kernel input to the independent Monster rank filter.
-/

public section
noncomputable section
open Module
open Atlas.Lattices Atlas.Conway
namespace Sporadic.Monster.Construction.QuasithinObstruction
open LocalC TrialitySpin LocalC.SourceNormalizer

private theorem spin_square_of_trivial_automorphism (f : spinNormalizer)
    (hf : f.val.2 = 1) : f ^ 2 = 1 := by
  let T : End ℝ SpinSpace := f.val.1.toLinearMap
  have hcomm (q : Q1Image) : T * SpinAction.imageRepresentation q =
      SpinAction.imageRepresentation q * T := by
    apply LinearMap.ext
    intro v
    have h := f.prop.1 q v
    rw [hf] at h
    exact h
  have hcomm_all (S : End ℝ SpinSpace) : T * S = S * T := by
    have hS : S ∈ Submodule.span ℝ (Set.range
        (SpinAction.imageRepresentation : Q1Image → End ℝ SpinSpace)) := by
      rw [spin_span]; trivial
    induction hS using Submodule.span_induction with
    | mem S h => obtain ⟨q, rfl⟩ := h; exact hcomm q
    | zero => simp
    | add S U _ _ hS hU => simp only [mul_add, add_mul, hS, hU]
    | smul c S _ hS => simp only [mul_smul_comm, smul_mul_assoc, hS]
  have hcenter : T ∈ Subalgebra.center ℝ (End ℝ SpinSpace) := by
    rw [Subalgebra.mem_center_iff]
    intro S
    exact (hcomm_all S).symm
  obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff ℝ).mp hcenter
  have hcv (v : SpinSpace) : f.val.1 v = c • v := by
    exact LinearMap.congr_fun hc v
  have hcsq : c * c = 1 := by
    let : Nontrivial SpinSpace := Module.nontrivial_of_finrank_pos (by
      rw [finrank_spinSpace]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (0 : SpinSpace)
    have hpos := bothAxesDomain.form_pos v hv
    have h := f.prop.2 v v
    simp only [hcv, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact mul_right_cancel₀ hpos.ne' (by simpa only [mul_assoc, one_mul] using h)
  apply spinNormalizer_ext
  apply LinearEquiv.ext
  intro v
  change f.val.1 (f.val.1 v) = v
  rw [hcv, hcv, smul_smul, hcsq, one_smul]

private theorem pullback_automorphism_square (x : localPullback)
    (hx : leechCentralProjection x.val.2 = 1) : x.val.1.val.2 ^ 2 = 1 := by
  have hg : x.val.2 = 1 ∨ x.val.2 = negationIsometry := by
    have hm : x.val.2 ∈ leechCentralProjection.ker := hx
    rwa [leechCentralProjection_kernel, leechCentralSigns_mem] at hm
  have hb : leechModTwoRepresentation x.val.2 = 1 :=
    (leechModTwoRepresentation_kernel x.val.2).mpr hg
  apply MulEquiv.ext
  intro q
  have h := x.prop q
  change latticeClass sourceLatticeComparison (x.val.1.val.2 q) =
    leechModTwoRepresentation x.val.2 (latticeClass sourceLatticeComparison q) at h
  rw [hb] at h
  rcases (latticeClass_eq_iff sourceLatticeComparison _ _).mp h with hq | hq
  · change x.val.1.val.2 (x.val.1.val.2 q) = q
    rw [hq, hq]
  · change x.val.1.val.2 (x.val.1.val.2 q) = q
    rw [hq, map_mul, automorphism_fixes_centerGenerator, hq, mul_assoc,
      ← pow_two, q1ImageCenterGenerator_sq, mul_one]

/-- A pullback element projecting to a scalar Leech sign has fourth power one. -/
theorem pullbackQuotient_kernel_pow_four (x : localPullback)
    (hx : leechCentralProjection x.val.2 = 1) : x ^ 4 = 1 := by
  have hspin : x.val.1 ^ 4 = 1 := by
    have h := spin_square_of_trivial_automorphism (x.val.1 ^ 2)
      (pullback_automorphism_square x hx)
    simpa only [← pow_mul] using h
  have hleech : x.val.2 ^ 4 = 1 := by
    have hm : x.val.2 ∈ leechCentralProjection.ker := hx
    rw [leechCentralProjection_kernel, leechCentralSigns_mem] at hm
    rcases hm with h | h
    · simp [h]
    · rw [h, show 4 = 2 * 2 from rfl, pow_mul, pow_two negationIsometry,
        negationIsometry_sq, one_pow]
  apply Subtype.ext
  exact Prod.ext hspin hleech

/-- The actual tensor-image quotient kernel has exponent dividing four. -/
theorem cToLeechQuotient_kernel_pow_four (c : C) (hc : cToLeechQuotient c = 1) : c ^ 4 = 1 := by
  obtain ⟨x, rfl⟩ := pullbackToC_surjective c
  rw [cToLeechQuotient_pullback] at hc
  rw [← map_pow, pullbackQuotient_kernel_pow_four x hc, map_one]

/-- The kernel in the actual tensor image C is a two-group. -/
theorem cToLeechQuotient_kernel_isTwoGroup : IsPGroup 2 cToLeechQuotient.ker := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro c
  refine ⟨2, Subtype.ext ?_⟩
  exact cToLeechQuotient_kernel_pow_four c.val c.prop

/-- The literal map on the embedded local subgroup has a two-group kernel. -/
theorem localToLeechQuotient_kernel_isTwoGroup : IsPGroup 2 localToLeechQuotient.ker := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro c
  refine ⟨2, Subtype.ext ?_⟩
  change c.val ^ 4 = 1
  apply cEquivLocalSubgroup.symm.injective
  rw [map_pow, map_one]
  exact cToLeechQuotient_kernel_pow_four _ c.prop

end Sporadic.Monster.Construction.QuasithinObstruction
