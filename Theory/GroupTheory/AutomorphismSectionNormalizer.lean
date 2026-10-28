module
public import Theory.GroupTheory.AutomorphismSectionKernel

/-!
# Stability of the two-section automorphism kernel

An automorphism preserving N also normalizes the automorphisms fixing N
and the quotient pointwise. This keeps the action kernel intrinsic and
avoids choosing a complement. Source application: the actual lift action
in Aschbacher–Smith C.1.35, printed p.138.
-/

@[expose] public section
namespace Subgroup
variable {E : Type*} [Group E]

private theorem conj_mem_sectionKernel (N : Subgroup E) (a b : MulAut E)
    (ha : ∀ x, x ∈ N ↔ a x ∈ N) (hb : b ∈ sectionKernel N) :
    a*b*a⁻¹ ∈ sectionKernel N := by
  constructor
  · intro x
    have hh := (ha _).mp (hb.1 (a⁻¹ x))
    simpa only [map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply,
      MulEquiv.apply_symm_apply] using hh
  · intro x hx
    have hax : a⁻¹ x ∈ N := (ha _).mpr (by simpa using hx)
    change a (b (a⁻¹ x)) = x
    rw [hb.2 _ hax]
    exact a.apply_symm_apply x

/-- An automorphism preserving the lower section normalizes the kernel on
both sections. -/
theorem mem_normalizer_sectionKernel (N : Subgroup E) (a : MulAut E)
    (ha : ∀ x, x ∈ N ↔ a x ∈ N) :
    a ∈ normalizer (sectionKernel N : Set (MulAut E)) := by
  apply mem_normalizer_iff.mpr
  intro b
  constructor
  · exact conj_mem_sectionKernel N a b ha
  · intro hb
    have ha' (x : E) : x ∈ N ↔ a⁻¹ x ∈ N := by
      simpa using (ha (a⁻¹ x)).symm
    have hh := conj_mem_sectionKernel N a⁻¹ (a*b*a⁻¹) ha' hb
    simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,inv_mul_cancel,mul_one] using hh
end Subgroup
