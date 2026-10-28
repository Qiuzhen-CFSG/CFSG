module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.SecondCoreCertificate

/-!
# Centralizing lifts of the binary linear Levi generators

The Weyl reflection r₈ and the corrected unipotent s₃s₇s₈ centralize the
literal six-step short commutator. The correction s₃s₇ lies in the radical,
so these two checked words retain the complete linear quotient image.
Source: F.4.27(4)(ii) and J.4.7, printed p.444.
-/

public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.Atlas
open OuterOddSubgroups.OverlapCentralizers

private theorem val_mul (x y : Atlas1600Group) : (x*y).val=x.val*y.val := rfl
private theorem val_inv (x : Atlas1600Group) : x⁻¹.val=x.val⁻¹ := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem short_reflection_commutes :
    Commute (a .r8) (a .s7*a .s4*(a .s7)⁻¹) := by
  apply Subtype.ext
  simp only [a,val_mul,val_inv,atlas1600ParrottAssignment_val,Atlas1600ParrottData.permutation]
  have h : Packed.perm 1*(Packed.perm 8*Packed.perm 5*(Packed.perm 8)⁻¹) =
      (Packed.perm 8*Packed.perm 5*(Packed.perm 8)⁻¹)*Packed.perm 1 := by
    apply Equiv.ext
    apply Atlas1600ParrottData.allFin
    decide +kernel
  simpa [Packed.perm_eq,Packed.generator] using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem short_corrected_commutes :
    Commute (a .s3*a .s7*a .s8) (a .s7*a .s4*(a .s7)⁻¹) := by
  apply Subtype.ext
  simp only [a,val_mul,val_inv,atlas1600ParrottAssignment_val,Atlas1600ParrottData.permutation]
  have h : (Packed.perm 4*Packed.perm 8*Packed.perm 9)*
      (Packed.perm 8*Packed.perm 5*(Packed.perm 8)⁻¹) =
      (Packed.perm 8*Packed.perm 5*(Packed.perm 8)⁻¹)*
        (Packed.perm 4*Packed.perm 8*Packed.perm 9) := by
    apply Equiv.ext
    apply Atlas1600ParrottData.allFin
    decide +kernel
  simpa [Packed.perm_eq,Packed.generator] using h

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.Atlas
