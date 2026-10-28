module

public import Theory.SpecificGroups.Suzuki.MaximalNonsplitTori
public import Theory.GroupTheory.SubgroupPartitionCounting
import Mathlib.Tactic

/-!
# The Suzuki nonsplit partition counting identity

Count the nonidentity elements in the partition by conjugates of the root
group, split torus, and maximal nonsplit representatives. A subgroup `U`
contributes `[G : N(U)] (|U| - 1)` elements. Dividing by `|G|`, inserting
the root/Borel and split-normalizer orders, and rearranging gives equation
(*) of Huppert--Blackburn, *Finite Groups III*, XI.3.10(i), pp. 192--193.
Neither the number of nonsplit classes nor their individual orders is assumed.
-/

namespace BenderSuzuki.MatrixGroups

private theorem nonsplit_card_ne_borel_divisor {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalNonsplit m U)
    {n : ℕ} (hn : n ∣ (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1)) :
    Nat.card U ≠ n := by
  intro heq
  have hone := Nat.eq_one_of_dvd_coprimes (suzukiOvoid_degree_coprime_borel m)
    hU.card_dvd (heq ▸ hn)
  exact hU.ne_bot hm (Subgroup.card_eq_one.mp hone)

private theorem nonsplit_card_ne_root {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalNonsplit m U) :
    Nat.card U ≠ Nat.card (SuzukiRootSubgroup m) := by
  rw [suzukiRootSubgroup_card m hm]
  exact nonsplit_card_ne_borel_divisor hm hU (dvd_mul_right _ _)

private theorem nonsplit_card_ne_split {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalNonsplit m U) :
    Nat.card U ≠ Nat.card (SuzukiSplitTorus m) := by
  rw [suzukiSplitTorus_card m hm]
  exact nonsplit_card_ne_borel_divisor hm hU (dvd_mul_left _ _)

private theorem root_card_ne_split (m : ℕ) (hm : 0 < m) :
    Nat.card (SuzukiRootSubgroup m) ≠ Nat.card (SuzukiSplitTorus m) := by
  rw [suzukiRootSubgroup_card m hm, suzukiSplitTorus_card m hm]
  have hq : 1 < (2 : ℕ) ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
  have hsub : 2 ^ (2 * m + 1) - 1 < 2 ^ (2 * m + 1) := Nat.sub_lt (by omega) (by decide)
  nlinarith

open Classical in
private theorem representatives_with_split_root_not_conjugate {m : ℕ} (hm : 0 < m)
    (R : SuzukiNonsplitRepresentatives m) :
    ∀ U ∈ insert (SuzukiRootSubgroup m) (insert (SuzukiSplitTorus m) R.subgroups),
    ∀ V ∈ insert (SuzukiRootSubgroup m) (insert (SuzukiSplitTorus m) R.subgroups),
    (∃ g : SuzukiMatrixGroup m, V = U.map (MulAut.conj g).toMonoidHom) → U = V := by
  classical
  intro U hU V hV hconj
  have hc : Nat.card U = Nat.card V := by
    obtain ⟨g, rfl⟩ := hconj
    exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
  simp only [Finset.mem_insert] at hU hV
  rcases hU with rfl | rfl | hU <;> rcases hV with rfl | rfl | hV
  · rfl
  · exact (root_card_ne_split m hm hc).elim
  · exact (nonsplit_card_ne_root hm (R.maximal V hV) hc.symm).elim
  · exact (root_card_ne_split m hm hc.symm).elim
  · rfl
  · exact (nonsplit_card_ne_split hm (R.maximal V hV) hc.symm).elim
  · exact (nonsplit_card_ne_root hm (R.maximal U hU) hc).elim
  · exact (nonsplit_card_ne_split hm (R.maximal U hU) hc).elim
  · by_contra hne
    exact R.not_conjugate U hU V hV hne hconj

/-- The normalized nonsplit contribution to the Suzuki subgroup partition.
Here the relative index is the order of the normalizer quotient. -/
public theorem SuzukiNonsplitRepresentatives.normalized_counting_identity
    {m : ℕ} (hm : 0 < m) (R : SuzukiNonsplitRepresentatives m) :
    (∑ U ∈ R.subgroups, ((Nat.card U : ℚ) - 1) /
      ((U.relIndex (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) : ℚ) *
        (Nat.card U : ℚ))) =
    (2 ^ (2 * m + 1) : ℚ) * (2 ^ (2 * m + 1) - 1) /
      (2 * ((2 ^ (2 * m + 1)) ^ 2 + 1)) := by
  classical
  let S := insert (SuzukiRootSubgroup m) (insert (SuzukiSplitTorus m) R.subgroups)
  have hP (x : SuzukiMatrixGroup m) (hx : x ≠ 1) :
      ∃! V : Subgroup (SuzukiMatrixGroup m),
        (∃ U ∈ S, ∃ g : SuzukiMatrixGroup m, V = U.map (MulAut.conj g).toMonoidHom) ∧ x ∈ V := by
    simpa only [S, Finset.mem_insert, exists_eq_or_imp, or_and_right, exists_or, exists_eq_left]
      using R.partition_existsUnique hm x hx
  have hcount := Subgroup.sum_card_sub_one_div_normalizer_card_of_partition S
    (representatives_with_split_root_not_conjugate hm R) hP
  have hroot : SuzukiRootSubgroup m ∉ insert (SuzukiSplitTorus m) R.subgroups := by
    simp only [Finset.mem_insert, not_or]
    refine ⟨fun heq => root_card_ne_split m hm (congrArg (fun U : Subgroup (SuzukiMatrixGroup m) => Nat.card U) heq), ?_⟩
    intro h
    exact nonsplit_card_ne_root hm (R.maximal _ h) rfl
  have hsplit : SuzukiSplitTorus m ∉ R.subgroups := by
    intro h
    exact nonsplit_card_ne_split hm (R.maximal _ h) rfl
  dsimp only [S] at hcount
  rw [Finset.sum_insert hroot, Finset.sum_insert hsplit] at hcount
  have hnormalizer (U : Subgroup (SuzukiMatrixGroup m)) :
      ((U.relIndex (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)))) : ℚ) *
        (Nat.card U : ℚ) = (Nat.card (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) : ℚ) := by
    exact_mod_cast Subgroup.relIndex_mul_card_of_le (Subgroup.le_normalizer (H := U))
  simp_rw [hnormalizer]
  rw [suzukiRootSubgroup_card m hm, suzukiRootSubgroup_normalizer m hm,
    suzukiBorelSubgroup_card m hm, suzukiSplitTorus_card m hm,
    suzukiSplitTorus_normalizer_card m hm, suzukiMatrixGroup_card m hm] at hcount
  have hqNat : 1 < (2 : ℕ) ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
  push_cast [Nat.cast_sub hqNat.le] at hcount
  have hq : (1 : ℚ) < 2 ^ (2 * m + 1) := by exact_mod_cast hqNat
  have hq0 : (2 : ℚ) ^ (2 * m + 1) ≠ 0 := by positivity
  have hqm : (2 : ℚ) ^ (2 * m + 1) - 1 ≠ 0 := by linarith
  have hqd : ((2 : ℚ) ^ (2 * m + 1)) ^ 2 + 1 ≠ 0 := by positivity
  linear_combination (norm := (field_simp; ring)) hcount

end BenderSuzuki.MatrixGroups
