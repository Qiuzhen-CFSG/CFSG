module
public import Theory.GroupAction.MaximalCosetOrbit
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A centralizer after adjoining a prime-index supplement

If T centralizes Z≤E and Z has prime relative index in E, any v∈E\Z
supplements Z. Thus C_T(v)=C_T(E). The proof uses subgroup generation
and centralizer duality, without finiteness or a normality assumption.

The original A₅ flag applies this with |Z|=2 and |E|=4 to the two points
outside its fixed line. Source: Aschbacher–Smith 13.2.11(4), p.881.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem inf_centralizer_eq_of_prime_index_supplement
    (T Z E : Subgroup G) (hZE : Z ≤ E) {p : ℕ} (hp : p.Prime)
    (hi : Z.relIndex E = p) (hTZ : T ≤ centralizer (Z : Set G))
    (v : G) (hv : v ∈ E) (hvZ : v ∉ Z) :
    T ⊓ centralizer ({v} : Set G) = T ⊓ centralizer (E : Set G) := by
  have hgen : Z ⊔ zpowers v = E := sup_zpowers_eq_of_relIndex_prime hZE hp hi hv hvZ
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    apply le_centralizer_iff.mpr
    rw [← hgen]
    apply sup_le
    · exact le_centralizer_iff.mp (inf_le_left.trans hTZ)
    · apply zpowers_le.mpr
      intro t ht
      exact mem_centralizer_singleton_iff.mp ht.2
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hv))
end Subgroup
