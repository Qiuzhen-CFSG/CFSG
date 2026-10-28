module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# Selecting a nontrivial binary product projection

A nontrivial subgroup of a two-factor product has a nontrivial coordinate.
For an elementary binary subgroup, that projection has order two or at
least four. These are the two genuine paired E.2.7 witness alternatives.
-/

public section
open Subgroup
namespace Subgroup
variable {G A H : Type*} [Group G] [Group A] [Group H]

theorem fst_ne_bot_or_snd_ne_bot (V : Subgroup (G × A)) (hv : V ≠ ⊥) :
    V.map (MonoidHom.fst G A) ≠ ⊥ ∨ V.map (MonoidHom.snd G A) ≠ ⊥ := by
  by_contra! hh
  apply hv
  apply eq_bot_iff.mpr
  intro x hx
  apply Prod.ext
  · exact mem_bot.mp (hh.1 ▸ mem_map_of_mem (MonoidHom.fst G A) hx)
  · exact mem_bot.mp (hh.2 ▸ mem_map_of_mem (MonoidHom.snd G A) hx)

theorem two_or_four_of_elementary_ne_bot [Finite G] (V : Subgroup G)
    [IsElementaryAbelian 2 V] (hv : V ≠ ⊥) : Nat.card V = 2 ∨ 4 ≤ Nat.card V := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hn0 : n ≠ 0 := by
    intro he
    apply hv
    exact card_eq_one.mp (by simpa only [he,pow_zero] using hn)
  by_cases he : n=1
  · left
    simpa only [he,pow_one] using hn
  · right
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤n)
end Subgroup
