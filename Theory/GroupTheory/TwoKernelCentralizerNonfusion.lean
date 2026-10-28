module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Centralizers through a two-element kernel

If u and zu are not conjugate, a quotient map with kernel {1,z} carries
the full centralizer of u onto the full centralizer of its image. A lift
centralizing that image conjugates u either to u or to zu; nonfusion
excludes the second case.

Source application: Aschbacher--Smith F.5.5, printed p.301.
-/

public section
open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer_eq_of_two_kernel_nonfusion (q : G →* H)
    (hq : Function.Surjective q) (z u : G)
    (hk : ∀ x ∈ q.ker, x = 1 ∨ x = z) (hnot : ¬ IsConj u (z*u)) :
    (centralizer ({u} : Set G)).map q = centralizer ({q u} : Set H) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg q (mem_centralizer_singleton_iff.mp hx)
  · intro y hy
    obtain ⟨g,rfl⟩ := hq y
    have hc := mem_centralizer_singleton_iff.mp hy
    have hker : g*u*g⁻¹*u⁻¹ ∈ q.ker := by
      change q (g*u*g⁻¹*u⁻¹)=1
      rw [map_mul,map_mul,map_mul,map_inv,map_inv,hc]
      simp only [mul_inv_cancel_right,mul_inv_cancel]
    have hgu : g*u*g⁻¹=u := by
      rcases hk _ hker with he | he
      · exact mul_inv_eq_one.mp he
      · apply False.elim
        apply hnot
        exact isConj_iff.mpr ⟨g,mul_inv_eq_iff_eq_mul.mp he⟩
    exact ⟨g,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgu),rfl⟩

end MonoidHom
