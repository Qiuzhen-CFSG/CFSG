module
public import Theory.Representation.PSL3Two.NaturalOrbits
public import Mathlib.GroupTheory.Coset.Card

/-!
# Small invariant subgroups in natural binary linear-three modules

A nonzero SL₃(2)-invariant subgroup of the natural three-space contains every
nonzero vector, by transitivity, and therefore has order eight. Consequently
an invariant subgroup of order at most four is trivial. Applying the statement
to the two coordinate projections proves the corresponding result for two
identically marked natural summands.

This is used to prove properness of the actual plane stabilizer in the
natural and doubled alternatives of Aschbacher–Smith 13.6.22, printed p.932.
-/

public section
open Subgroup Representation
namespace BinaryLinearThree

/-- The natural action has no nontrivial invariant subgroup of order at most four. -/
theorem natural_small_invariant_eq_bot
    (H : Subgroup (Multiplicative Vector)) (hc : Nat.card H ≤ 4)
    (hn : ∀ g : Group, ∀ x : H, Multiplicative.ofAdd (W g x.val.toAdd) ∈ H) : H = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  change x = 1
  by_contra hx1
  have htop : H = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    by_cases hy : y = 1
    · exact hy ▸ H.one_mem
    obtain ⟨g, hg⟩ := natural_transitive_nonzero x.toAdd y.toAdd hx1 hy
    have he : Multiplicative.ofAdd (W g x.toAdd) = y := hg
    exact he ▸ hn g ⟨x, hx⟩
  have hcard : Nat.card (⊤ : Subgroup (Multiplicative Vector)) = 8 := by
    rw [card_top, Nat.card_eq_fintype_card]
    decide +kernel
  rw [htop, hcard] at hc
  omega

private def firstProjection : Multiplicative (Vector × Vector) →* Multiplicative Vector :=
  (LinearMap.fst (ZMod 2) Vector Vector).toAddMonoidHom.toMultiplicative
private def secondProjection : Multiplicative (Vector × Vector) →* Multiplicative Vector :=
  (LinearMap.snd (ZMod 2) Vector Vector).toAddMonoidHom.toMultiplicative

private theorem image_card_le {A B : Type*} [_root_.Group A] [_root_.Group B] [Finite A]
    (H : Subgroup A) (f : A →* B) : Nat.card (H.map f) ≤ Nat.card H :=
  Nat.card_le_card_of_surjective (f.subgroupMap H) (f.subgroupMap_surjective H)

/-- The same small-subgroup obstruction holds in two identical natural summands. -/
theorem doubled_small_invariant_eq_bot
    (H : Subgroup (Multiplicative (Vector × Vector))) (hc : Nat.card H ≤ 4)
    (hn : ∀ g : Group, ∀ x : H,
      Multiplicative.ofAdd ((W.prod W) g x.val.toAdd) ∈ H) : H = ⊥ := by
  have h₁ : H.map firstProjection = ⊥ := by
    apply natural_small_invariant_eq_bot _ ((image_card_le H firstProjection).trans hc)
    rintro g ⟨y, x, hx, rfl⟩
    exact mem_map_of_mem firstProjection (hn g ⟨x, hx⟩)
  have h₂ : H.map secondProjection = ⊥ := by
    apply natural_small_invariant_eq_bot _ ((image_card_le H secondProjection).trans hc)
    rintro g ⟨y, x, hx, rfl⟩
    exact mem_map_of_mem secondProjection (hn g ⟨x, hx⟩)
  apply le_bot_iff.mp
  intro x hx
  have hx₁ : firstProjection x ∈ (⊥ : Subgroup (Multiplicative Vector)) := h₁ ▸ mem_map_of_mem firstProjection hx
  have hx₂ : secondProjection x ∈ (⊥ : Subgroup (Multiplicative Vector)) := h₂ ▸ mem_map_of_mem secondProjection hx
  change x = 1
  exact Prod.ext hx₁ hx₂
end BinaryLinearThree
