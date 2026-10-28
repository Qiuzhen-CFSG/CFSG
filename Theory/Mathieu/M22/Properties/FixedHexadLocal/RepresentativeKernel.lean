module
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel.Enumeration

/-!
# The representative fixed-hexad kernel is characteristic

Inside the centralizer of the standard involution, the pointwise fixed-hexad
kernel consists exactly of the elements commuting with all their conjugates.
Normality and abelianness give one inclusion; the certified enumeration of the
actual degree-22 centralizer gives the other. This intrinsic description is
preserved by every automorphism of the centralizer.

This is the representative calculation for the M22 local argument associated
with Aschbacher--Smith 1.1.5(3)(f), printed p.502, and 2.3.9(7)(f), printed
pp.525--526. No identification with the centralizer's two-core is assumed.
-/

public section
namespace Sporadic.Mathieu
open Subgroup M22RepresentativeKernel

/-- The standard fixed-hexad kernel is detected by commuting with every
conjugate inside the involution centralizer. -/
theorem m22GeneratorA_fixedPoints_kernel_mem_iff
    (x : centralizer ({m22GeneratorAInM22} : Set M22)) :
    x.val ∈ m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22) ↔
      ∀ y : centralizer ({m22GeneratorAInM22} : Set M22),
        x * (y * x * y⁻¹) = (y * x * y⁻¹) * x := by
  constructor
  · intro hx y
    let K := (m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22)).subgroupOf C
    have hn : K.Normal := m22FixedPoints_kernel_normal _ representative_order
    let := m22HexadPointwiseKernel_elementaryAbelian
      (m22FixedPoints_mem_blocks _ representative_order)
    exact congrArg Subtype.val (mul_comm'
      (⟨x, hx⟩ : K) ⟨y * x * y⁻¹, hn.conj_mem x hx y⟩)
  · exact mem_kernel_of_commutes_conjugates x

/-- Characteristicity is relative to the actual involution centralizer. -/
theorem m22GeneratorA_fixedPoints_kernel_characteristic :
    ((m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22)).subgroupOf
      (centralizer ({m22GeneratorAInM22} : Set M22))).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  apply (m22GeneratorA_fixedPoints_kernel_mem_iff (a x)).mpr
  intro y
  have he := congrArg a
    ((m22GeneratorA_fixedPoints_kernel_mem_iff x).mp hx (a.symm y))
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using he

end Sporadic.Mathieu
