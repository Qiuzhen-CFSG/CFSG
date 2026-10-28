module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Powerset


set_option maxRecDepth 100000

/-!
# Common finite Steiner-system interfaces

This module supplies the reusable finite Steiner-system interface for the
Mathieu models listed in GLS Number 3, Part I, Chapter A, Tables 5.3a--5.3e
(printed pages 262--266; PDF pages 279--283).  The concrete systems and their
automorphism groups remain in the individual group modules and must follow
the GLS-cited Aschbacher/Atlas constructions.

Moved here from `KGroup.Sporadic.Mathieu.SteinerSystem`; the declarations now
live in the reusable `Theory.GroupTheory` namespace.
-/
namespace Theory.GroupTheory

/-- A finite Steiner system with blocks of size `k` and unique extension of
`t`-subsets. -/
public structure SteinerSystem (α : Type*) [Fintype α] [DecidableEq α]
    (t k : ℕ) where
  blocks : Finset (Finset α)
  block_card : ∀ B ∈ blocks, B.card = k
  steiner : ∀ (S : Finset α), S.card = t →
    (blocks.filter (fun B => S ⊆ B)).card = 1

/-- A finite packing with the exact Steiner count is a Steiner system.
The intersection hypothesis gives uniqueness; the binomial count gives coverage. -/
@[expose]
public def SteinerSystem.ofPairwiseIntersection
    {α : Type*} [Fintype α] [DecidableEq α] {t k : ℕ}
    (blocks : Finset (Finset α))
    (blockCard : ∀ B ∈ blocks, B.card = k)
    (interCard : ∀ B₁ ∈ blocks, ∀ B₂ ∈ blocks,
      B₁ ≠ B₂ → (B₁ ∩ B₂).card < t)
    (count : blocks.card * Nat.choose k t = Nat.choose (Fintype.card α) t) :
    SteinerSystem α t k where
  blocks := blocks
  block_card := blockCard
  steiner := by
    have hDisjoint :
        (blocks : Set (Finset α)).PairwiseDisjoint
          (fun B => B.powersetCard t) := by
      intro B₁ hB₁ B₂ hB₂ hne
      change Disjoint (B₁.powersetCard t) (B₂.powersetCard t)
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hSInter : S ⊆ B₁ ∩ B₂ :=
        Finset.subset_inter
          (Finset.mem_powersetCard.mp hS₁).1
          (Finset.mem_powersetCard.mp hS₂).1
      have hCardLe : t ≤ (B₁ ∩ B₂).card := by
        rw [← (Finset.mem_powersetCard.mp hS₁).2]
        exact Finset.card_le_card hSInter
      exact (Nat.not_le_of_gt (interCard B₁ hB₁ B₂ hB₂ hne)) hCardLe
    have hCover :
        blocks.biUnion (fun B => B.powersetCard t) =
          (Finset.univ : Finset α).powersetCard t := by
      apply Finset.eq_of_subset_of_card_le
      · intro S hS
        obtain ⟨B, _hB, hSPower⟩ := Finset.mem_biUnion.mp hS
        exact Finset.mem_powersetCard.mpr
          ⟨fun _ _ => Finset.mem_univ _, (Finset.mem_powersetCard.mp hSPower).2⟩
      · rw [Finset.card_biUnion hDisjoint, Finset.card_powersetCard,
          Finset.card_univ]
        apply le_of_eq
        calc
          Nat.choose (Fintype.card α) t =
              blocks.card * Nat.choose k t := count.symm
          _ = ∑ _B ∈ blocks, Nat.choose k t := by simp
          _ = ∑ B ∈ blocks, Nat.choose B.card t := by
            apply Finset.sum_congr rfl
            intro B hB
            rw [blockCard B hB]
          _ = ∑ B ∈ blocks, (B.powersetCard t).card := by
            simp only [Finset.card_powersetCard]
    intro S hSCard
    have hSCover : S ∈ blocks.biUnion (fun B => B.powersetCard t) := by
      rw [hCover]
      exact Finset.mem_powersetCard_univ.mpr hSCard
    obtain ⟨B, hB, hSPower⟩ := Finset.mem_biUnion.mp hSCover
    have hSB : S ⊆ B := (Finset.mem_powersetCard.mp hSPower).1
    apply Finset.card_eq_one.mpr
    refine ⟨B, ?_⟩
    ext C
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hC
      by_contra hCB
      have hSInter : S ⊆ C ∩ B := Finset.subset_inter hC.2 hSB
      have hCardLe : t ≤ (C ∩ B).card := by
        rw [← hSCard]
        exact Finset.card_le_card hSInter
      exact (Nat.not_le_of_gt (interCard C hC.1 B hB hCB)) hCardLe
    · rintro rfl
      exact ⟨hB, hSB⟩
/-- The block field of the pairwise-intersection constructor is the supplied block set. -/
@[simp]
public theorem SteinerSystem.ofPairwiseIntersection_blocks
    {α : Type*} [Fintype α] [DecidableEq α] {t k : ℕ}
    (blocks : Finset (Finset α))
    (blockCard : ∀ B ∈ blocks, B.card = k)
    (interCard : ∀ B₁ ∈ blocks, ∀ B₂ ∈ blocks,
      B₁ ≠ B₂ → (B₁ ∩ B₂).card < t)
    (count : blocks.card * Nat.choose k t = Nat.choose (Fintype.card α) t) :
    (SteinerSystem.ofPairwiseIntersection blocks blockCard interCard count).blocks = blocks :=
  rfl
open scoped Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The setwise automorphism group of a finite Steiner system. -/
public def SteinerSystem.aut {t k : ℕ} (S : SteinerSystem α t k) : Subgroup (Equiv.Perm α) :=
  MulAction.stabilizer (Equiv.Perm α) (S.blocks : Set (Finset α))

/-- Membership in the Steiner-system automorphism group is setwise block preservation. -/
public theorem SteinerSystem.mem_aut_iff {t k : ℕ} (S : SteinerSystem α t k) (g : Equiv.Perm α) :
    g ∈ S.aut ↔ g • (S.blocks : Set (Finset α)) = (S.blocks : Set (Finset α)) := by
  rw [SteinerSystem.aut, MulAction.mem_stabilizer_iff]

end Theory.GroupTheory
