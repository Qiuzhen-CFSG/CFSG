module

public import Theory.GroupTheory.SteinerSystem
public import Mathlib.Data.Finset.Card

/-!
# Unique completion and residual partitions in Steiner systems

The unique-extension axiom identifies blocks containing the same `t`-subset.
Consequently, blocks through a `(t - 1)`-subset partition its complement after
that common subset is removed. These are direct consequences of the defining
Steiner-system axioms, independent of a particular model.
-/

namespace Theory.GroupTheory.SteinerSystem

variable {α : Type*} [Fintype α] [DecidableEq α] {t k : ℕ}

/-- Every `t`-subset has a unique containing block. -/
public theorem existsUnique_block (D : SteinerSystem α t k)
    (S : Finset α) (hS : S.card = t) : ∃! B, B ∈ D.blocks ∧ S ⊆ B := by
  simpa only [Finset.mem_filter] using
    Finset.card_eq_one_iff_existsUnique.mp (D.steiner S hS)

/-- Two blocks containing the same `t`-subset coincide. -/
public theorem block_eq_of_subset (D : SteinerSystem α t k)
    {S B C : Finset α} (hS : S.card = t)
    (hB : B ∈ D.blocks) (hC : C ∈ D.blocks) (hSB : S ⊆ B) (hSC : S ⊆ C) :
    B = C :=
  (D.existsUnique_block S hS).unique ⟨hB, hSB⟩ ⟨hC, hSC⟩

/-- Distinct blocks intersect in fewer than `t` points. -/
public theorem inter_card_lt (D : SteinerSystem α t k)
    {B C : Finset α} (hB : B ∈ D.blocks) (hC : C ∈ D.blocks) (hne : B ≠ C) :
    (B ∩ C).card < t := by
  by_contra h
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
  exact hne (D.block_eq_of_subset hcard hB hC
    (hS.trans Finset.inter_subset_left) (hS.trans Finset.inter_subset_right))

/-- Removing a common `t`-subset from blocks of an `S(t+1,k,α)` gives
pairwise disjoint sets, each of size `k-t`, covering the complementary points. -/
public theorem residual_partition (D : SteinerSystem α (t + 1) k)
    (T : Finset α) (hT : T.card = t) :
    (∀ B ∈ D.blocks.filter (T ⊆ ·), (B \ T).card = k - t) ∧
    (↑(D.blocks.filter (T ⊆ ·)) : Set (Finset α)).PairwiseDisjoint (· \ T) ∧
    (D.blocks.filter (T ⊆ ·)).biUnion (· \ T) = Finset.univ \ T := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨hB, hTB⟩ := Finset.mem_filter.mp hB
    rw [Finset.card_sdiff_of_subset hTB, D.block_card B hB, hT]
  · intro B hB C hC hne
    obtain ⟨hB, hTB⟩ := Finset.mem_filter.mp hB
    obtain ⟨hC, hTC⟩ := Finset.mem_filter.mp hC
    apply Finset.disjoint_left.mpr
    intro x hxB hxC
    obtain ⟨hxB, hxT⟩ := Finset.mem_sdiff.mp hxB
    obtain ⟨hxC, _⟩ := Finset.mem_sdiff.mp hxC
    exact hne (D.block_eq_of_subset (S := insert x T)
      (by rw [Finset.card_insert_of_notMem hxT, hT]) hB hC
      (Finset.insert_subset hxB hTB) (Finset.insert_subset hxC hTC))
  · ext x
    constructor
    · intro hx
      obtain ⟨B, _, hxB⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hxB).2⟩
    · intro hx
      have hxT := (Finset.mem_sdiff.mp hx).2
      obtain ⟨B, ⟨hB, hTB⟩, _⟩ := D.existsUnique_block (insert x T)
        (by rw [Finset.card_insert_of_notMem hxT, hT])
      exact Finset.mem_biUnion.mpr ⟨B,
        Finset.mem_filter.mpr ⟨hB, Finset.insert_subset_iff.mp hTB |>.2⟩,
        Finset.mem_sdiff.mpr ⟨hTB (Finset.mem_insert_self _ _), hxT⟩⟩

/-- Inclusion between Steiner systems with the same parameters is equality.
The hypothesis `t ≤ k` ensures each block contains a `t`-subset. -/
public theorem blocks_eq_of_subset (D E : SteinerSystem α t k) (htk : t ≤ k)
    (hDE : D.blocks ⊆ E.blocks) : D.blocks = E.blocks := by
  apply Finset.Subset.antisymm hDE
  intro B hB
  obtain ⟨S, hSB, hS⟩ := Finset.exists_subset_card_eq
    (show t ≤ B.card by rw [E.block_card B hB]; exact htk)
  obtain ⟨C, ⟨hC, hSC⟩, _⟩ := D.existsUnique_block S hS
  have hCB := E.block_eq_of_subset hS (hDE hC) hB hSC hSB
  simpa only [hCB] using hC

end Theory.GroupTheory.SteinerSystem
