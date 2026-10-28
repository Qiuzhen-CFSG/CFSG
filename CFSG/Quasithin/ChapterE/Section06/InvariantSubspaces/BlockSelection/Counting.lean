module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.ThreeElements

/-!
# Counting the blocks in E.6.14

Two commuting chi-zero blocks supply independent three-elements, hence an
actual elementary nine. This proves the rank-at-most-one branch without any
model-action input. In the faithful-action branch the elementary argument
uses a fixed nine to contradict the rank bound in N_G(W).

`FixedNineInput` remains an explicit obligation in the second branch: the
block permutation and automorphism calculations must construct that nine.
No residual or unique-maximal assertion is inferred just from this count.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.14,
printed p.251 (PDF p.262), using E.6.7 on printed p.246 (PDF p.257).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem BlockFamily.count_pos {H M : Subgroup G} (d : BlockFamily H M)
    (hescape : ¬ H ≤ M) : 0 < d.count := by
  by_contra hn
  have he : (⨆ i, d.block i) = ⊥ := by
    apply le_antisymm _ bot_le
    apply iSup_le
    intro i
    have := i.isLt
    omega
  apply hescape
  rw [d.generated, he, sup_bot_eq]
  exact inf_le_right

theorem BlockFamily.count_eq_one_of_rank {H M : Subgroup G} (d : BlockFamily H M)
    (hescape : ¬ H ≤ M) (hrank : primeRank 3 H ≤ 1) : d.count = 1 := by
  have hp := d.count_pos hescape
  by_contra hn
  have htwo : 2 ≤ d.count := by omega
  let i : Fin d.count := ⟨0, by omega⟩
  let j : Fin d.count := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  have hr := two_le_threeRank_of_commuting_blocks (d.type i) (d.type j)
    (d.commuting i j hij) (d.le i) (d.le j)
  omega

theorem BlockFamily.count_eq_one_of_faithful_three
    {K : GroupClass} {T : Sylow 2 G} {M V W : Subgroup G}
    (h : HypothesisE61 K T M V) (hW : W ∈ obstructionFamily M V)
    (hc : HasCharacteristicTwo (centralizer (W : Set G)))
    (hfixed : FixedNineInput G) (d : BlockFamily (centralizer (W : Set G)) M)
    (ha : HasFaithfulThreeAction W) : d.count = 1 := by
  have hp := d.count_pos hW.2.2.1
  by_contra hn
  have htwo : 2 ≤ d.count := by omega
  let i : Fin d.count := ⟨0, by omega⟩
  let j : Fin d.count := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  obtain ⟨x, hxN, hxo, hxC⟩ := ha.exists_element
  have hnormal : ((centralizer (W : Set G)).subgroupOf
      (normalizer (W : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_le_normalizer_centralizer W)
  obtain ⟨E, hE, hcard, hEH, hfix⟩ := hfixed
    (normalizer (W : Set G)) (centralizer (W : Set G)) (d.block i) (d.block j)
    (Subgroup.centralizer_le_normalizer _) hnormal hc
    (normalizer_threeRank_le_two h hW.2.1 hW.1)
    (d.le i) (d.le j) (d.type i) (d.type j) (d.subnormal i) (d.subnormal j)
    (d.commuting i j hij) x hxN hxo
  let := hE
  exact no_fixed_nine h hW.2.1 hW.1 hcard hEH hxN hxo hxC hfix

theorem BlockFamily.count_eq_one
    {K : GroupClass} {T : Sylow 2 G} {M V W : Subgroup G}
    (h : HypothesisE61 K T M V) (hW : W ∈ obstructionFamily M V)
    (hc : HasCharacteristicTwo (centralizer (W : Set G)))
    (hfixed : FixedNineInput G) (d : BlockFamily (centralizer (W : Set G)) M)
    (hthree : ThreeCondition W) : d.count = 1 := by
  rcases hthree with hr | ha
  · exact d.count_eq_one_of_rank hW.2.2.1 hr
  · exact d.count_eq_one_of_faithful_three h hW hc hfixed ha

omit [Finite G] in
theorem BlockFamily.generated_of_count_eq_one {H M : Subgroup G} (d : BlockFamily H M)
    (hcount : d.count = 1) (i : Fin d.count) : H = (H ⊓ M) ⊔ d.block i := by
  have hgen : (⨆ j, d.block j) = d.block i := by
    apply le_antisymm _ (le_iSup d.block i)
    apply iSup_le
    intro j
    have hj : j = i := by
      apply Fin.ext
      have := j.isLt
      have := i.isLt
      omega
    rw [hj]
  exact d.generated.trans (congrArg _ hgen)

omit [Finite G] in
theorem BlockFamily.exists_single {H M : Subgroup G} (d : BlockFamily H M)
    (hcount : d.count = 1) (hescape : ¬ H ≤ M) :
    ∃ L : Subgroup G, L ≤ H ∧ H = (H ⊓ M) ⊔ L ∧
      ChapterC.IsChiZeroBlock L ∧ (L.subgroupOf H).IsSubnormal ∧ ¬ L ≤ M := by
  let i : Fin d.count := ⟨0, by omega⟩
  have hg := d.generated_of_count_eq_one hcount i
  refine ⟨d.block i, d.le i, hg, d.type i, d.subnormal i, ?_⟩
  intro hi
  apply hescape
  rw [hg]
  exact sup_le inf_le_right hi

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
