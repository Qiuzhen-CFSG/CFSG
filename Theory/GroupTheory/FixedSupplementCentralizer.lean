module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Fixed subgroups in a normalized product

If Z normalizes V and centralizes R, then C_{ZV}(R)=Z C_V(R).
A second elementary product argument shows that a supplement
U=C_Z(L)V containing Z, with Z∩V centralized by L, forces U=ZV and [Z,L]=1.
Both statements use literal subgroup joins and require no ambient normality.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
12.4.5--6, printed pp.813--814. Here V denotes the whole original module,
not its fixed line C_V(L).
-/

public section
open Subgroup
open scoped Pointwise

namespace Subgroup
variable {G : Type*} [Group G]

/-- Fixed subgroups split over a factor already centralized by R. -/
theorem inf_centralizer_sup_of_centralizing (Z V R : Subgroup G)
    (hZV : Z ≤ normalizer (V : Set G))
    (hZR : Z ≤ centralizer (R : Set G)) :
    (Z ⊔ V) ⊓ centralizer (R : Set G) = Z ⊔ (V ⊓ centralizer (R : Set G)) := by
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (Z : Set G) * (V : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right Z V hZV]
      exact hx.1
    obtain ⟨z,hz,v,hv,rfl⟩ := hxprod
    have hvc : v ∈ centralizer (R : Set G) := by
      simpa using (centralizer (R : Set G)).mul_mem
        ((centralizer (R : Set G)).inv_mem (hZR hz)) hx.2
    exact mul_mem_sup hz ⟨hv,hvc⟩
  · exact sup_le (le_inf le_sup_left hZR)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

/-- A fixed supplement and a fixed intersection force all of Z to be fixed. -/
theorem centralizes_of_fixed_supplement (Z V L U : Subgroup G)
    (hZU : Z ≤ U) (hZV : Z ≤ normalizer (V : Set G))
    (hUV : U = (Z ⊓ centralizer (L : Set G)) ⊔ V)
    (hfix : Z ⊓ V ≤ centralizer (L : Set G)) :
    U = Z ⊔ V ∧ Z ≤ centralizer (L : Set G) := by
  have hU : U = Z ⊔ V := by
    apply le_antisymm
    · rw [hUV]
      exact sup_le_sup inf_le_left le_rfl
    · exact sup_le hZU (hUV.symm ▸ le_sup_right)
  refine ⟨hU, ?_⟩
  intro z hz
  have hzn : Z ⊓ centralizer (L : Set G) ≤ normalizer (V : Set G) :=
    inf_le_left.trans hZV
  have hp : z ∈ ((Z ⊓ centralizer (L : Set G) : Subgroup G) : Set G) * (V : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hzn, ← hUV]
    exact hZU hz
  obtain ⟨c,hc,v,hv,he⟩ := hp
  have hvZ : v ∈ Z := by
    have hh := Z.mul_mem (Z.inv_mem hc.1) hz
    rw [← he] at hh
    simpa only [inv_mul_cancel_left] using hh
  rw [← he]
  exact (centralizer (L : Set G)).mul_mem hc.2 (hfix ⟨hvZ,hv⟩)
end Subgroup
