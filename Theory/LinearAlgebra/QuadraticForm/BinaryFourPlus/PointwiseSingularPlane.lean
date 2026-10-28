module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.FixedSingularPlane

/-! The binary plus-space pointwise plane stabilizer is detected by the
faithful factor-swap projection. This avoids any further finite certificate.
Source: Aschbacher–Smith 14.3.19, the factor centralizer calculation. -/

public section
open Subgroup Module
namespace BinaryFourPlus
/-- The pointwise stabilizer of a singular plane has at most two elements. -/
theorem eq_one_or_eq_of_fixed_singular_plane (a b:Wreath) (S:Submodule (ZMod 2) V)
    (hd:2≤finrank (ZMod 2) S) (hs:∀v∈S,q v=0)
    (ha:a≠1) (hi:∀v∈S,(wreathToIsometry a).val v=v)
    (hb:∀v∈S,(wreathToIsometry b).val v=v) : b=1 ∨ b=a := by
  classical
  by_cases hb1:b=1
  · exact Or.inl hb1
  right
  have hpa := (fixed_singular_plane a ha S hd hs hi).1
  have hpb := (fixed_singular_plane b hb1 S hd hs hb).1
  have hpab:a.right=b.right := by
    have hh:∀x y:C2,x≠1→y≠1→x=y := by decide
    exact hh _ _ hpa hpb
  have hab:a⁻¹*b=1 := by
    by_contra hh
    have hfix:∀v∈S,(wreathToIsometry (a⁻¹*b)).val v=v := by
      intro v hv
      rw [map_mul,map_inv]
      change (wreathToIsometry a).val.symm ((wreathToIsometry b).val v)=v
      rw [hb v hv]
      apply (wreathToIsometry a).val.injective
      rw [LinearEquiv.apply_symm_apply,hi v hv]
    have hx := (fixed_singular_plane (a⁻¹*b) hh S hd hs hfix).1
    apply hx
    change RegularWreathProduct.rightHom (a⁻¹*b)=1
    rw [map_mul,map_inv]
    change a.right⁻¹*b.right=1
    rw [hpab,inv_mul_cancel]
  exact (inv_mul_eq_one.mp hab).symm
end BinaryFourPlus
