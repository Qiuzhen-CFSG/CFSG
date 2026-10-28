module
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers.ExpandedStructure
import Mathlib.Tactic
/-!
# Forty-eight words in the centralizer of the triple transposition

The paired A₄, a swap of two pairs, and the triple transposition provide 48
words. Their distinct images on three selected points prove injectivity.
The independently known centralizer order proves completeness. Checking these
words then proves normalization and the required containment of cubic elements.
All finite calculations are checked by the kernel.

Source: Aschbacher–Smith 15.3.43, printed p.1140.
-/

@[expose] public section
open Equiv Subgroup
namespace AlternatingSeven.ThreeResidualLocals

def pairSwap : Perm7 := swap 0 2 * swap 1 3

def pairedCosetRep : Fin 4 → Perm7 := ![1, pairSwap, pairing, pairSwap * pairing]

def pairedWord (i : Fin 12 × Fin 4) : Perm7 :=
  words12 pairedThree fourFlip i.1 * pairedCosetRep i.2

theorem pairedWord_injective : Function.Injective pairedWord := by
  have h : Function.Injective (fun i =>
      (pairedWord i 0, pairedWord i 2, pairedWord i 4)) := by decide +kernel
  intro i j hij
  apply h
  exact congrArg (fun g : Perm7 => (g 0, g 2, g 4)) hij

theorem pairedWord_mem_centralizer (i : Fin 12 × Fin 4) :
    pairedWord i ∈ centralizer ({pairing} : Set Perm7) := by
  apply mem_centralizer_singleton_iff.mpr
  decide +revert +kernel

theorem pairedWord_surjective : Function.Surjective
    (fun i : Fin 12 × Fin 4 =>
      (⟨pairedWord i, pairedWord_mem_centralizer i⟩ : centralizer ({pairing} : Set Perm7))) := by
  apply (Function.Injective.bijective_of_nat_card_le ?_ ?_).2
  · intro i j h
    exact pairedWord_injective (congrArg Subtype.val h)
  · rw [centralizer_pairing_card, Nat.card_prod]
    simp

theorem mem_centralizer_pairing_iff_word (g : Perm7) :
    g ∈ centralizer ({pairing} : Set Perm7) ↔ ∃ i, pairedWord i = g := by
  constructor
  · intro hg
    obtain ⟨i, hi⟩ := pairedWord_surjective ⟨g, hg⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · rintro ⟨i, rfl⟩
    exact pairedWord_mem_centralizer i

theorem pairedWord_mem_normalizer (i : Fin 12 × Fin 4) :
    pairedWord i ∈ normalizer (pairedFour : Set Perm7) := by
  change pairedWord i ∈ normalizer (closure {pairedThree, fourFlip} : Set Perm7)
  rw [mem_normalizer_pair_closure_iff]
  change pairedWord i * pairedThree * (pairedWord i)⁻¹ ∈ pairedFour ∧
    pairedWord i * fourFlip * (pairedWord i)⁻¹ ∈ pairedFour
  rw [pairedFour_eq_explicit]
  decide +revert +kernel

theorem pairedWord_cube_mem (i : Fin 12 × Fin 4)
    (hi : pairedWord i ^ 3 = 1) : pairedWord i ∈ pairedFour := by
  rw [pairedFour_eq_explicit]
  decide +revert +kernel

end AlternatingSeven.ThreeResidualLocals
