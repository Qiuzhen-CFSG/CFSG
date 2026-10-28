module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.ZMod

/-!
# Fixed vectors in binary involutory extensions

If a normal subgroup fixes a nonzero vector and an involution represents the
other coset, the whole group fixes a nonzero vector. The sum of the vector
with its involutory translate works unless it vanishes; in characteristic two,
vanishing means the original vector is already fixed.

Applied to the representation on linear maps to a dual, this extends an
invariant pairing from the alternating subgroup to the symmetric group.
Source application: Aschbacher–Smith, 14.7.71(1), printed p.1075.
-/

public section

open Subgroup
namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A binary fixed vector survives extension by an involutory coset representative. -/
theorem exists_fixed_ne_zero_of_involutory_extension
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    (t : G) (ht : t * t = 1) (hcoset : ∀ g : G, g ∈ N ∨ g * t ∈ N)
    (v : V) (hv : v ≠ 0) (hNv : ∀ n ∈ N, ρ n v = v) :
    ∃ w : V, w ≠ 0 ∧ ∀ g : G, ρ g w = w := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have extend (w : V) (hNw : ∀ n ∈ N, ρ n w = w) (htw : ρ t w = w) :
      ∀ g : G, ρ g w = w := by
    intro g
    rcases hcoset g with hg | hg
    · exact hNw g hg
    · have he := hNw (g * t) hg
      simpa only [map_mul, Module.End.mul_apply, htw] using he
  have hNtv (n : G) (hn : n ∈ N) : ρ n (ρ t v) = ρ t v := by
    have hc := hNv (t * n * t) (by
      simpa only [htinv] using (inferInstance : N.Normal).conj_mem n hn t)
    have he : n * t = t * (t * n * t) := by rw [← mul_assoc, ← mul_assoc, ht, one_mul]
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hc]
  by_cases hz : v + ρ t v = 0
  · refine ⟨v, hv, extend v hNv ?_⟩
    have he := eq_neg_of_add_eq_zero_left hz
    simpa only [ZModModule.neg_eq_self] using he.symm
  · refine ⟨v + ρ t v, hz, extend _ ?_ ?_⟩
    · intro n hn
      rw [map_add, hNv n hn, hNtv n hn]
    · rw [map_add, ← Module.End.mul_apply, ← map_mul, ht, map_one]
      exact add_comm _ _
end Representation
