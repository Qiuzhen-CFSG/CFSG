module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.WordCertificate
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed

/-!
# The centered long-root endpoint is a positive radical word

The actual Weyl conjugate (r₁r₈)r₅(r₁r₈)⁻¹ is the positive word with
normal-form index757. Its s₈ coordinate is zero, allowing the fixed root
support to place it in the linear radical. The faithful Atlas equality is
kernel checked, independently of any assertion about the path distance.
Source: Aschbacher--Smith J.4.7, printed p.444.
-/

public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.Atlas
open OuterOddSubgroups.OverlapCentralizers

private theorem val_mul (x y : Atlas1600Group) : (x*y).val=x.val*y.val := rfl
private theorem val_inv (x : Atlas1600Group) : x⁻¹.val=x.val⁻¹ := rfl
private theorem val_pow (x : Atlas1600Group) (n : ℕ) : (x^n).val=x.val^n := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem leftWord_positive : leftWord =
    a .s1 * a .s3 * a .s4 * a .s5^3 * a .s6 * a .s7^2 := by
  apply Subtype.ext
  simp only [leftWord,a,atlas1600R5_eq,val_mul,val_inv,val_pow,
    atlas1600ParrottAssignment_val,Atlas1600ParrottData.permutation]
  have h : (Packed.perm 0 * Packed.perm 1) * (Packed.perm 2 * Packed.perm 6^2) *
      (Packed.perm 0 * Packed.perm 1)⁻¹ =
      Packed.perm 2 * Packed.perm 4 * Packed.perm 5 * Packed.perm 6^3 *
        Packed.perm 7 * Packed.perm 8^2 := by
    apply Equiv.ext
    apply Atlas1600ParrottData.allFin
    decide +kernel
  simpa [Packed.perm_eq,Packed.generator] using h

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.Atlas
