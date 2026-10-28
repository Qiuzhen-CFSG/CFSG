module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The four-core of S4 in small quotients

The normal Klein four is minimal normal and self-centralizing, so every
nontrivial normal subgroup of S4 contains it. Hence any homomorphism from S4
to a finite group of order less than 24 kills that four-core. This avoids
classifying homomorphisms or assuming the image normal in the target.
The source 13.9.10 application maps its actual S4 into C_G(z)/Q of order12.
-/

public section
namespace Theory.SpecificGroups.SymmetricFour
open Subgroup
open Theory.SpecificGroups.SymmetricSix.DuadCalculation

theorem twoCore_le_normal_of_ne_bot (N:Subgroup Four) [N.Normal] (hne:N≠⊥) :
    pCore 2 Four≤N := by
  rw [←core_eq]
  rcases normal_subgroup_core (N⊓core) inf_le_right with h|h
  · have hc:⁅N,core⁆=⊥ := le_bot_iff.mp ((le_inf (commutator_le_left _ _)
        (commutator_le_right _ _)).trans_eq h)
    have hN:N≤core := by
      rw [←centralizer_core]
      exact commutator_eq_bot_iff_le_centralizer.mp hc
    exact (hne ((inf_eq_left.mpr hN).symm.trans h)).elim
  · exact h ▸ inf_le_left

theorem twoCore_le_ker_of_card_lt {H:Type*} [Group H] [Finite H]
    (f:Four→*H) (hcard:Nat.card H<24) : pCore 2 Four≤f.ker := by
  apply twoCore_le_normal_of_ne_bot
  intro h
  have hi:=f.ker_eq_bot_iff.mp h
  have hc:=Nat.card_le_card_of_injective f hi
  have hfour:Nat.card Four=24 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  rw [hfour] at hc
  exact (not_le_of_gt hcard) hc

theorem twoCore_le_ker_of_equiv_of_card_lt {X H:Type*} [Group X] [Group H] [Finite H]
    (e:X≃*Four) (f:X→*H) (hcard:Nat.card H<24) : pCore 2 X≤f.ker := by
  have hh:=twoCore_le_ker_of_card_lt (f.comp e.symm.toMonoidHom) hcard
  intro x hx
  have hx':e x∈pCore 2 Four := by
    rw [←pCore_map_iso 2 e]
    exact mem_map_of_mem _ hx
  have he:=hh hx'
  change f (e.symm (e x))=1 at he
  change f x=1
  simpa only [e.symm_apply_apply] using he
end Theory.SpecificGroups.SymmetricFour
