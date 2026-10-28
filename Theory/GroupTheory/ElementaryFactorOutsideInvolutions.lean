module
public import Theory.GroupTheory.QuaternionFactorJoinNormalizer
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Index

/-! In an index-two elementary extension of U, a square-one element a*u forces
u fixed modulo the center. The actual fixed-space containment therefore puts
every outside involution in A. Source:14.3.18(6). -/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G:Type*} [Group G]

theorem outside_involution_mem_factor_of_inverse_bound
    (U A:Subgroup G) [IsElementaryAbelian 2 A]
    (hn:A≤normalizer (U:Set G))
    (hfix:∀a∈A,a∉U→∀u∈U,a*u*a⁻¹=u⁻¹→u∈A)
    (x:G) (hx:x∈A⊔U) (hxU:x∉U) (hx2:x^2=1) : x∈A := by
  have hxprod:x∈(A:Set G)*(U:Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right A U hn]
    exact hx
  obtain ⟨a,ha,u,hu,rfl⟩:=hxprod
  have haU:a∉U := by
    intro hh
    exact hxU (U.mul_mem hh hu)
  have ha2:a^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha
  have hai:a⁻¹=a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha2)
  have hxi:(a*u)⁻¹=a*u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx2)
  have hi:a*u*a⁻¹=u⁻¹ := by
    calc
      a*u*a⁻¹=(a*u)⁻¹*a⁻¹ := by rw [hxi]
      _=u⁻¹ := by rw [mul_inv_rev,hai]; simpa only [←mul_assoc,pow_two,mul_one] using congrArg (fun z=>u⁻¹*z) ha2
  exact A.mul_mem ha (hfix a ha haU u hu hi)
end Subgroup
