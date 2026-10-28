module
public import Theory.GroupTheory.PRadical.NormalComponentImages
public import Theory.GroupTheory.PCorePrimeToIndex
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Saturation of cores of subgroups of prime-to-p index

If A has index prime to p, its p-core is the p-core of its full normalizer.
Indeed A lies in that normalizer with index prime to p, so the normalizer
core lies in O_p(A). The reverse inclusion is automatic. This retains the
original subgroup witness when passing to a normal ambient section.

Source: the odd-index radical comparison used in MS93 (3.7), p.872.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem pCoreIn_normalizer_eq_of_prime_not_dvd_index
    (A : Subgroup G) (hindex : ¬ p ∣ A.index) :
    (normalizer (A.pCoreIn p : Set G)).pCoreIn p = A.pCoreIn p := by
  let N := normalizer (A.pCoreIn p : Set G)
  have hAN : A ≤ N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore p A))
  have hi : ¬ p ∣ (A.subgroupOf N).index := fun hd =>
    hindex (hd.trans (relIndex_dvd_index_of_le hAN))
  have hm := map_mono (f := N.subtype)
    (pCore_le_map_pCore_of_prime_not_dvd_index (A.subgroupOf N) hi)
  change N.pCoreIn p ≤ ((A.subgroupOf N).pCoreIn p).map N.subtype at hm
  rw [pCoreIn_subgroupOf p A N hAN,
    map_subgroupOf_eq_of_le ((A.pCoreIn_le p).trans hAN)] at hm
  exact le_antisymm hm (le_map_pCore_normalizer (isPGroup_pCoreIn p A))

end Subgroup
