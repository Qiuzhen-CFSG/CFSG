module

public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer
/-!
# Order and orbit size of the nonsingular A₈ stabilizer

Restriction to the two marked points has the pointwise A₆ fixer as kernel.
A double transposition exchanging those points supplies the nonidentity
image. Thus the stabilizer has order 720 and index 28, using the original
natural-module action and no enumeration of permutations or subgroups.

Source: Aschbacher–Smith, the Sylow arrangement at the opening of
Theorem 12.6.2, printed pp.823–824 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup BinaryPermutation
open BinaryPermutation.EightNonsingular

namespace BinaryPermutation.EightNonsingular
private def swapLift (i j k l : Fin 8) : Equiv.Perm (Fin 8) := Equiv.swap i j * Equiv.swap k l

private theorem swapLift_pair (i j k l : Fin 8)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    coreRepresentation (Fin 8) (swapLift i j k l) (pair i j) = pair i j := by
  rw [pair_action]
  have hi : swapLift i j k l i = j := by
    simp [swapLift, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hki.symm hli.symm]
  have hj : swapLift i j k l j = i := by
    simp [swapLift, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hkj.symm hlj.symm]
  rw [hi,hj]
  apply Subtype.ext
  exact add_comm _ _

theorem pairRestriction_ker (i j : Fin 8) (hij : i ≠ j) :
    (pairRestriction i j hij).ker =
      (pointFixer i j).subgroupOf (stabilizer (coreToNatural (Fin 8) (pair i j))) := by
  ext g
  change pairRestriction i j hij g = 1 ↔ ∀ k : ({i,j} : Set (Fin 8)), g.val.val k.val = k.val
  constructor
  · intro h k
    exact congrArg Subtype.val (DFunLike.congr_fun h k)
  · intro h
    apply Equiv.ext
    intro k
    exact Subtype.ext (h k)

theorem pairRestriction_surjective (i j : Fin 8) (hij : i ≠ j) :
    Function.Surjective (pairRestriction i j hij) := by
  classical
  let X := ({i,j} : Set (Fin 8))
  have hX : Fintype.card X = 2 := by simp [X,hij]
  let f := pairRestriction i j hij
  have hc : Nat.card (Equiv.Perm X) = 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,hX]; decide
  have hne : f.range ≠ ⊥ := by
    have hpair : ({i,j} : Finset (Fin 8)).card < (Finset.univ : Finset (Fin 8)).card := by
      have hb := Finset.card_le_two (a := i) (b := j)
      simp only [Finset.card_univ,Fintype.card_fin]; omega
    obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hpair
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
    obtain ⟨hki,hkj⟩ := hk
    obtain ⟨l,_,hl⟩ := (Finset.exists_mem_notMem_of_card_lt_card
      (show ({i,j,k} : Finset (Fin 8)).card < (Finset.univ : Finset (Fin 8)).card from by
        have h₁ := Finset.card_insert_le i ({j,k} : Finset (Fin 8))
        have h₂ := Finset.card_le_two (a := j) (b := k)
        simp only [Finset.card_univ,Fintype.card_fin]; omega))
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hl
    let a : alternatingGroup (Fin 8) := ⟨swapLift i j k l, by
      rw [Equiv.Perm.mem_alternatingGroup]
      simp [swapLift,Equiv.Perm.sign_swap hij,Equiv.Perm.sign_swap (Ne.symm hl.2.2)]⟩
    have ha : a ∈ stabilizer (coreToNatural (Fin 8) (pair i j)) :=
      (pair_fixed_iff a i j).mpr (swapLift_pair i j k l hki hkj hl.1 hl.2.1)
    let b : stabilizer (coreToNatural (Fin 8) (pair i j)) := ⟨a,ha⟩
    intro hz
    have hb : f b = 1 := mem_bot.mp (hz.le (show f b ∈ f.range from ⟨b,rfl⟩))
    have hh := congrArg (fun p : Equiv.Perm X => (p ⟨i,Or.inl rfl⟩).val) hb
    change swapLift i j k l i = i at hh
    have hi : swapLift i j k l i = j := by
      simp [swapLift,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne (Ne.symm hki) (Ne.symm hl.1)]
    exact hij (hi.symm.trans hh).symm
  have hdiv : Nat.card f.range ∣ 2 := by
    have hh := f.range.card_subgroup_dvd_card
    change Nat.card f.range ∣ Nat.card (Equiv.Perm X) at hh
    rwa [hc] at hh
  have hr : Nat.card f.range = 2 := by
    have hgt := (one_lt_card_iff_ne_bot f.range).mpr hne
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h <;> omega
  exact MonoidHom.range_eq_top.mp (f.range.eq_top_of_card_eq (hr.trans hc.symm))

theorem pair_stabilizer_card (i j : Fin 8) (hij : i ≠ j) :
    Nat.card (stabilizer (coreToNatural (Fin 8) (pair i j))) = 720 := by
  let f := pairRestriction i j hij
  have hk : Nat.card f.ker = 360 := by
    rw [pairRestriction_ker, Nat.card_congr
      (subgroupOfEquivOfLe (pointFixer_le_stabilizer i j)).toEquiv,
      Nat.card_congr (pointFixerEquiv i j hij).toEquiv,
      nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hi : f.ker.index = 2 := by
    rw [index_ker, f.range_eq_top_of_surjective (pairRestriction_surjective i j hij),card_top,
      Nat.card_eq_fintype_card,Fintype.card_perm]
    simp [hij]
  have hh := f.ker.card_mul_index
  rw [hk,hi] at hh
  exact hh.symm

theorem nonsingular_stabilizer_index (w : W)
    (hw : TerminalOrthogonal.Eight.form w ≠ 0) : (stabilizer w).index = 28 := by
  obtain ⟨i,j,hij,rfl⟩ := nonsingular_pair w hw
  have hh := (stabilizer (coreToNatural (Fin 8) (pair i j))).card_mul_index
  rw [pair_stabilizer_card i j hij,nat_card_alternatingGroup,Nat.card_fin] at hh
  norm_num [Nat.factorial] at hh
  omega
end BinaryPermutation.EightNonsingular
