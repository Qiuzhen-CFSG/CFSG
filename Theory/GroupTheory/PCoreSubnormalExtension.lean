module
public import Theory.GroupTheory.PCoreSubnormalSupplement
public import Theory.GroupTheory.PCorePrimeToIndex

/-!
# The two-core of a subnormal radical extension

If P has odd index and O₂(P) normalizes a subnormal X, the restriction
P intersect X O₂(P) still has odd index and two-core O₂(P). Restricting
the two-core of the extension therefore puts it in O₂(P).

Source application: the individual block extension in Aschbacher--Smith
preliminary15.2.23, printed p.1115.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem subnormal_twoCore_extension_le (X P : Subgroup G) (hX : X.IsSubnormal)
    (hP : Odd P.index) (hQX : P.pCoreIn 2 ≤ normalizer (X : Set G)) :
    (X ⊔ P.pCoreIn 2).pCoreIn 2 ≤ P.pCoreIn 2 := by
  let E := X ⊔ P.pCoreIn 2
  have hi := odd_index_subnormal_core_supplement X P hX hQX hP
  have hc : pCore 2 E ≤ (P.pCoreIn 2).subgroupOf E := by
    rw [←pCoreIn_subnormal_core_supplement X P hX hQX]
    exact pCore_le_map_pCore_of_prime_not_dvd_index _ hi.not_two_dvd_nat
  have hm := map_mono (f := E.subtype) hc
  rwa [map_subgroupOf_eq_of_le le_sup_right] at hm
end Subgroup
