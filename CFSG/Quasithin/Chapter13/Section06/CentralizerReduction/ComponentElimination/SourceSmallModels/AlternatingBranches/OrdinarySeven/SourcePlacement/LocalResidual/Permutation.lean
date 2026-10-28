module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual.PermutationContract
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups.Placement
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# The solvable permutation calculation in the ordinary A₇ argument

The normalizer of the three disjoint transpositions is precisely the
three-pair partition stabilizer. Its even part E is solvable and has order
dividing 48. If E normalizes a solvable subgroup D of A₇, then DE is solvable.
The fixed-coordinate solvable-overgroup calculation places DE in the
four-plus-three or three-pair stabilizer. The even paired three-cycle in E
excludes the former. Thus D ≤ E; if three divides |D|, its index divides 16.

Only the intrinsic permutation submodules of Section 8 are imported. Their
project dependency closure has no Section 6 module, so this reuse introduces
no cycle and does not use the later source theorem 13.8.24 as a hypothesis.
The existing short-word certificates supply the solvable-overgroup calculation;
no new enumeration of all subgroups is required.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932 (PDF p.949); the same seven-point calculation
appears in the proof of 13.8.24, printed pp.958–959.
-/

public section
open Subgroup Equiv Equiv.Perm
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
private def pairKernel : Subgroup S7 where
  carrier := {g | ∀ i, pairBlock (g i) = pairBlock i}
  one_mem' _ := rfl
  mul_mem' ha hb i := (ha _).trans (hb i)
  inv_mem' := by
    intro a ha i
    exact (ha (a⁻¹ i)).symm.trans (congrArg pairBlock (a.apply_symm_apply i))

private theorem transpositions_le_kernel : threeTranspositions ≤ pairKernel := by
  rw [threeTranspositions, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl <;> change ∀ i, _ <;> intro i <;> fin_cases i <;> decide

private theorem swap_mem_of_same_pair (i j : Fin 7) (h : pairBlock i = pairBlock j) :
    swap i j ∈ threeTranspositions := by
  have h01 : swap (0 : Fin 7) 1 ∈ threeTranspositions := subset_closure (by simp)
  have h23 : swap (2 : Fin 7) 3 ∈ threeTranspositions := subset_closure (by simp)
  have h45 : swap (4 : Fin 7) 5 ∈ threeTranspositions := subset_closure (by simp)
  fin_cases i <;> fin_cases j <;> norm_num [pairBlock] at h <;>
    simp only [swap_self] <;> first
    | exact threeTranspositions.one_mem
    | exact h01
    | exact h23
    | exact h45
    | rw [swap_comm]; exact h01
    | rw [swap_comm]; exact h23
    | rw [swap_comm]; exact h45

private theorem normalizer_preserves_pairs (n : S7)
    (hn : n ∈ normalizer (threeTranspositions : Set S7))
    (i j : Fin 7) (h : pairBlock i = pairBlock j) : pairBlock (n i) = pairBlock (n j) := by
  have hc := (mem_normalizer_iff.mp hn (swap i j)).mp (swap_mem_of_same_pair i j h)
  have he := transpositions_le_kernel hc (n i)
  simpa using he.symm

private theorem normalizer_le_pairStabilizer :
    normalizer (threeTranspositions : Set S7) ≤ pairStabilizer := by
  intro n hn i j
  constructor
  · intro h
    have he := normalizer_preserves_pairs n⁻¹ ((normalizer _).inv_mem hn) (n i) (n j) h
    simpa using he
  · exact normalizer_preserves_pairs n hn i j

private theorem pairStabilizer_le_normalizer :
    pairStabilizer ≤ normalizer (threeTranspositions : Set S7) := by
  rw [threeTranspositions, le_normalizer_closure_iff]
  intro n hn g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  all_goals
    rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]
    apply swap_mem_of_same_pair
    exact (hn _ _).mpr (by decide)

private theorem even_le_pairs : evenPairNormalizer ≤ pairStabilizer :=
  inf_le_right.trans normalizer_le_pairStabilizer

private theorem even_card_dvd : Nat.card evenPairNormalizer ∣ 48 := by
  simpa only [pairStabilizer_card] using card_dvd_of_le even_le_pairs

private theorem even_solvable : Group.IsSolvable evenPairNormalizer := by
  apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  have h : p ∣ 2 ^ 4 * 3 := hd.trans even_card_dvd
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)

private theorem even_not_fourThree : ¬ evenPairNormalizer ≤ fourThreeStabilizer := by
  let c : S7 := (swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5)
  have hc : c ∈ evenPairNormalizer := by
    refine ⟨?_, pairStabilizer_le_normalizer ?_⟩
    · change Perm.sign c = 1
      decide +kernel
    · decide +kernel
  intro h
  have he := (mem_fourThree_coord c).mp (h hc) 2 (by decide)
  change 4 < 4 at he
  omega

theorem permutation_local_statement : PermutationLocalStatement := by
  intro D hDa hDs hD3 hDn
  let : Group.IsSolvable D := hDs
  let : Group.IsSolvable evenPairNormalizer := even_solvable
  let : Group.IsSolvable (D ⊔ evenPairNormalizer : Subgroup S7) :=
    Group.isSolvable_sup_of_normalizes D evenPairNormalizer hDn
  have hT : ∀ g ∈ standardTwo, g ∈ alternatingGroup (Fin 7) →
      g ∈ D ⊔ evenPairNormalizer := by
    intro g hg ha
    exact mem_sup_right ⟨ha, pairStabilizer_le_normalizer hg.2⟩
  have hDP : D ≤ pairStabilizer := by
    rcases solvable_overgroup_standardEvenTwo_placement (D ⊔ evenPairNormalizer) hT with h | h
    · exact (even_not_fourThree (le_sup_right.trans h)).elim
    · exact le_sup_left.trans h
  have hDE : D ≤ evenPairNormalizer := le_inf hDa (hDP.trans pairStabilizer_le_normalizer)
  refine ⟨hDE, ?_⟩
  have hcard : Nat.card D * D.relIndex evenPairNormalizer = Nat.card evenPairNormalizer := by
    have h := (D.subgroupOf evenPairNormalizer).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hDE).toEquiv] at h
    exact h
  have hm : Nat.card D * D.relIndex evenPairNormalizer ∣ 48 := by
    rw [hcard]
    exact even_card_dvd
  have hi : D.relIndex evenPairNormalizer ∣ 16 := by
    have hh : 3 * D.relIndex evenPairNormalizer ∣ 3 * 16 :=
      (mul_dvd_mul_right hD3 _).trans hm
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hh
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show D.relIndex evenPairNormalizer ∣ 2 ^ 4 from hi)
  exact ⟨n, hn⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
end
