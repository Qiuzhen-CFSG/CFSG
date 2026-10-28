module
public import Theory.GroupTheory.CentralQuotientAutomorphismFixedDerived
public import Theory.GroupTheory.Commutator.ThirdInverseConvention

/-!
# Central quotient inversion fixes the derived group

In a group of class at most two, an automorphism inducing inversion modulo
the center fixes every commutator: central factors do not affect commutation,
and inverting both inputs preserves a central commutator. Closure then fixes
the whole derived subgroup. No finiteness or coprimality is required.

Source application: Aschbacher–Smith, the extraspecial invariant-Sylow
construction preceding 12.2.22, printed p.803.
-/

public section
open Subgroup
open scoped commutatorElement
namespace MulAut
variable {K : Type*} [Group K]
/-- Inversion on the central quotient fixes the derived subgroup in class two. -/
theorem fixes_derived_of_inverts_mod_center (a : MulAut K)
    (hclass : _root_.commutator K ≤ center K)
    (hi : ∀ x : K, a x * x ∈ center K) :
    _root_.commutator K ≤ a.fixedSubgroup := by
  apply commutator_le.mpr
  intro x _ y _
  rw [MulAut.mem_fixedSubgroup, map_commutatorElement]
  have hq (z : K) : QuotientGroup.mk' (center K) (a z) =
      QuotientGroup.mk' (center K) z⁻¹ := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [div_eq_mul_inv, inv_inv] using hi z
  exact (CentralExtension.commutator_eq_of_image_eq (QuotientGroup.mk' (center K))
    (by rw [QuotientGroup.ker_mk']) (hq x) (hq y)).trans
    (commutator_inv_inv_of_mem_center x y
      (hclass (commutator_mem_commutator (mem_top _) (mem_top _))))
end MulAut
