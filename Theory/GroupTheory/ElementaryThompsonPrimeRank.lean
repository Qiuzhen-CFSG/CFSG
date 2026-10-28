module
public import Stellmacher.ElementaryAbelianMaxOrderSpecification
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Elementary Thompson subgroups at equal two-rank

The largest elementary abelian subgroup of a finite group has order 2^m,
where m is its two-rank. Consequently, inclusion between subgroups of equal
two-rank preserves their maximum elementary families and their Thompson
subgroups. The equality of ranks is essential for this comparison.

Source application: Aschbacher--Smith, B.2.2--5 and 12.6.15, combined
manuscript of 1 March 2004, printed pp.75--76 and 826.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

theorem elementaryAbelianMaxOrder_eq_two_pow_primeRank (S : Subgroup G) :
    elementaryAbelianMaxOrder S = 2 ^ primeRank 2 S := by
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  let : IsElementaryAbelian 2 A := hA.2.1
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hu : Nat.card A ≤ 2 ^ primeRank 2 S := by
    let : IsElementaryAbelian 2 (A.subgroupOf S) := IsElementaryAbelian.subgroupOf hA.1
    have hh := (primeRank_le_iff_elementary_card_le (p := 2) S).mp le_rfl
      (A.subgroupOf S) inferInstance
    rwa [Nat.card_congr (subgroupOfEquivOfLe hA.1).toEquiv] at hh
  have hl : primeRank 2 S ≤ n := by
    apply (primeRank_le_iff_elementary_card_le S).mpr
    intro B hB
    have hh := hA.2.2 (B.map S.subtype) (map_subtype_le B) (hB.map S.subtype)
    rwa [card_map_of_injective S.subtype_injective,hn] at hh
  rw [hn] at hu
  have he : n = primeRank 2 S := le_antisymm
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hu) hl
  rw [←elementaryAbelianMaxSubgroups_card_eq S A hA,hn,he]

theorem elementaryAbelianMaxJ_le_of_primeRank_eq (P S : Subgroup G)
    (hPS : P ≤ S) (hr : primeRank 2 P = primeRank 2 S) :
    elementaryAbelianMaxJ P ≤ elementaryAbelianMaxJ S := by
  apply (elementaryAbelianMaxOrder_le_and_j_le_of_eq P S hPS).2
  rw [elementaryAbelianMaxOrder_eq_two_pow_primeRank,
    elementaryAbelianMaxOrder_eq_two_pow_primeRank,hr]
end Stellmacher
