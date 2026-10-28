module

public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadKernels
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions

/-!
# Discharging the native hexad restriction inputs

The intrinsic hexad kernels have just been identified with the pointwise octad
kernel. Their nonidentity elements are involutions fixing the deleted pair
pointwise, so the existing native involution calculation gives displacement
four on the M22 cocode. This constructs both earlier H.14 restriction inputs
used in H.15.2 and H.16.4, without assuming their kernel images or displacements.

Source: Aschbacher--Smith H.14.3(3), H.14.4(2--3), and H.15.2,
printed pp.397--399, combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22ChapterH.Hexad
open MathieuCode MathieuCode.Hexad
open MathieuCode.Hexad.CocodeAction.SixPointModel
open Representation.BinaryOffender

/-- Every nonidentity element of the inner hexad core is an involution. -/
theorem inner_kernel_orderOf (x : M22) (hx : x ∈ m22InnerHexadKernel O) (hne : x ≠ 1) :
    orderOf x = 2 := by
  let := inner_kernel_elementary
  exact orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian x hx, hne⟩

/-- Every nonidentity element of the outer hexad core is an involution. -/
theorem outer_kernel_orderOf (x : m22PairStabilizer)
    (hx : x ∈ m22OuterHexadKernel O) (hne : x ≠ 1) : orderOf x = 2 := by
  let := outer_kernel_elementary
  exact orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian x hx, hne⟩

/-- The inner H.14 displacement input on its literal cocode representation. -/
theorem inner_kernel_displacement (x : M22) (hx : x ∈ m22InnerHexadKernel O) (hne : x ≠ 1) :
    fixedCodim m22CocodeRepresentation (Subgroup.zpowers x) = 4 :=
  m22_cocode_involution_displacement x (inner_kernel_orderOf x hx hne)

/-- The outer hexad core still fixes both deleted points; it has inner displacement. -/
theorem outer_kernel_displacement (x : m22PairStabilizer)
    (hx : x ∈ m22OuterHexadKernel O) (hne : x ≠ 1) :
    fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers x) = 4 := by
  have hm : x.val ∈ octadPointwiseKernel O := by
    rw [← outer_kernel_image]
    exact Subgroup.mem_map_of_mem _ hx
  exact m22Outer_cocode_involution_displacement_of_fixed_zero x
    (outer_kernel_orderOf x hx hne)
    ((mem_octadPointwiseKernel O x.val).mp hm 0 (by decide +kernel))

/-- The actual earlier-source input consumed by the inner hexad transfer. -/
theorem innerRestriction : InnerRestrictionInput O :=
  innerRestrictionInput O inner_kernel_image inner_kernel_displacement

/-- The actual earlier-source input consumed by the outer hexad transfer. -/
theorem outerRestriction : OuterRestrictionInput O :=
  outerRestrictionInput O outer_kernel_image outer_kernel_displacement

end Sporadic.Mathieu.M22ChapterH.Hexad
end
