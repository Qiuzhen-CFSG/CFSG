module
public import Stellmacher.BaumannTwoOvergroupNormalizer
public import Stellmacher.SectionFiveToSeven.Defs
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# The direct two-subgroup normalizer step for a full Baumann commutator

Let S be the original ambient Sylow two-subgroup and K=[K,B(S)]. Every
two-subgroup normalized by K and B(S) normalizes K. Indeed its join with
B(S) is a two-group, so Baumann weak closure makes it normalize B(S),
and the full-commutator normalizer theorem applies. In particular the
two-core of any overgroup of K and B(S) normalizes K.

This is the local normalizer step in Stellmacher (5.2), Journal of Algebra
190 (1997), pp.28--29. It requires neither solvability nor characteristic
two of the overgroup. It does not assert K is subnormal in that overgroup.
-/
namespace Stellmacher.SectionsFiveToSeven
open Subgroup
universe u

public theorem normalized_two_subgroup_normalizes_full_baumann
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (K D : Subgroup G) (hD : IsPGroup 2 D)
    (hnorm : K ⊔ baumannIn (S : Subgroup G) ≤ normalizer (D : Set G))
    (hfull : K = ⁅K,baumannIn (S : Subgroup G)⁆) :
    D ≤ normalizer (K : Set G) := by
  let B := baumannIn (S : Subgroup G)
  have hB : IsPGroup 2 B := S.isPGroup'.to_le inf_le_left
  have hBD : B ≤ normalizer (D : Set G) := le_sup_right.trans hnorm
  have hjoin : IsPGroup 2 (D ⊔ B : Subgroup G) :=
    hD.to_sup_of_normal_left' hB hBD
  have hDB : D ≤ normalizer (B : Set G) := by
    apply le_sup_left.trans
    exact Stellmacher.twoSubgroup_le_normalizer_baumann S (D ⊔ B) hjoin le_sup_right
  exact twoSubgroup_le_normalizer_of_full_commutator K B D hB hD hnorm hDB hfull.symm

/-- The two-core of the genuine local overgroup normalizes the full commutator. -/
public theorem twoCore_normalizes_full_baumann
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (K M : Subgroup G) (hKM : K ≤ M) (hBM : baumannIn (S : Subgroup G) ≤ M)
    (hfull : K = ⁅K,baumannIn (S : Subgroup G)⁆) :
    twoCoreIn M ≤ normalizer (K : Set G) := by
  have hQM : twoCoreIn M ≤ M := map_subtype_le _
  have hn : ((twoCoreIn M).subgroupOf M).Normal := by
    rw [← comap_subtype, twoCoreIn, comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hMN := (normal_subgroupOf_iff_le_normalizer hQM).mp hn
  exact normalized_two_subgroup_normalizes_full_baumann S K (twoCoreIn M)
    (pCore_isPGroup.map M.subtype) ((sup_le hKM hBM).trans hMN) hfull

end Stellmacher.SectionsFiveToSeven
