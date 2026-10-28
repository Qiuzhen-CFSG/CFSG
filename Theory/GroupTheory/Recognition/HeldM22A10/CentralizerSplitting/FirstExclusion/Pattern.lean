module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Intrinsic data for the first nonsplit centralizer

The intended model has a binary character killing every involution and a
fourth root of its central involution outside the character kernel. For a
fourth-order element in the kernel whose square is not the central involution,
the square's centralizer has order 64 and every automorphism of that
centralizer fixes the original central involution.

These are finite, intrinsic proof obligations. They imply an ambient
contradiction by order-four transfer and the two-group normalizer condition,
as proved in `Criterion`. This module does not assert that the concrete first
model satisfies them. Square-root counts provide one way to prove the
necessary automorphism assertion.

Source problem: Huppert--Blackburn III, XII.1.18(b), p.314, citing Held,
J. Algebra 8 (1968), 436--449, DOI 10.1016/0021-8693(68)90054-9.
-/

namespace Theory.GroupTheory.HeldM22A10.FirstExclusion

/-- The binary target of the transfer character. -/
public abbrev Binary := Multiplicative (ZMod 2)

/-- Intrinsic finite-group facts sufficient for the first exclusion.
No ambient fusion or splitting conclusion occurs among these fields. -/
public structure Pattern (H : Type*) [Group H] where
  mark : H
  mark_sq : mark ^ 2 = 1
  mark_ne_one : mark ≠ 1
  mark_central : mark ∈ Subgroup.center H
  center_cases : ∀ w : H, w ∈ Subgroup.center H → w = 1 ∨ w = mark
  character : H →* Binary
  kills_involutions : ∀ w : H, w ^ 2 = 1 → character w = 1
  root : H
  root_sq : root ^ 2 = mark
  root_character : character root ≠ 1
  square_centralizers : ∀ w : H, character w = 1 → w ^ 2 ≠ 1 → w ^ 4 = 1 →
    w ^ 2 ≠ mark →
    Nat.card (Subgroup.centralizer ({w ^ 2} : Set H)) = 64 ∧
    ∀ z : Subgroup.centralizer ({w ^ 2} : Set H), (z : H) = mark →
      ∀ a : MulAut (Subgroup.centralizer ({w ^ 2} : Set H)), (a z : H) = mark

/-- The number of square roots of an element, computed inside its given group. -/
public noncomputable def squareRootCount {H : Type*} [Group H] (z : H) : ℕ :=
  Nat.card {x : H // x ^ 2 = z}

/-- Square-root counts are preserved by group isomorphisms. -/
public theorem squareRootCount_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (z : H) : squareRootCount (e z) = squareRootCount z := by
  symm
  apply Nat.card_congr
  refine e.toEquiv.subtypeEquiv ?_
  intro x
  change x ^ 2 = z ↔ (e x) ^ 2 = e z
  rw [← map_pow, e.injective.eq_iff]

/-- A square-root count distinguishing a nonidentity central element fixes it
under every automorphism. The first model uses count 20 in groups of order 64. -/
public theorem fixed_of_squareRootCount {H : Type*} [Group H]
    (z : H) (n : ℕ) (hz : z ∈ Subgroup.center H) (hz1 : z ≠ 1)
    (hcount : squareRootCount z = n)
    (hunique : ∀ w : H, w ∈ Subgroup.center H → w ≠ 1 →
      squareRootCount w = n → w = z) (a : MulAut H) : a z = z := by
  apply hunique
  · apply Subgroup.mem_center_iff.mpr
    intro w
    obtain ⟨v, rfl⟩ := a.surjective w
    simpa only [map_mul] using congrArg a (Subgroup.mem_center_iff.mp hz v)
  · intro he
    apply hz1
    apply a.injective
    simpa only [map_one] using he
  · rw [squareRootCount_equiv, hcount]

end Theory.GroupTheory.HeldM22A10.FirstExclusion
