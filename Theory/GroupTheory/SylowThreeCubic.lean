module

public import Mathlib.GroupTheory.Sylow

/-!
# Sylow three-subgroups in groups with cubic two-local index

If a finite group contains a two-subgroup of index three, every Sylow
three-subgroup has order three. Coprimeness makes its intersection with the
two-subgroup trivial; the relative-index inequality bounds its order by three,
while Sylow divisibility supplies the opposite inequality.

This is the elementary local order calculation used in Goldschmidt,
*Automorphisms of trivalent graphs* (1980), (2.16)(b), printed p.386.
-/

@[expose] public section
open Subgroup

namespace Subgroup

/-- A two-subgroup of index three forces every Sylow three-subgroup to have
order three. -/
theorem card_sylow_three_of_two_group_index_three {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (hS : IsPGroup 2 S) (hindex : S.index = 3) (P : Sylow 3 G) :
    Nat.card P = 3 := by
  have hd : Disjoint S (P : Subgroup G) :=
    hS.disjoint_of_coprime P.isPGroup' (by decide)
  have hle : Nat.card P ≤ 3 := by
    have h := Subgroup.relIndex_le_of_le_right (H := S)
      (show (P : Subgroup G) ≤ ⊤ from le_top)
      (by rw [relIndex_top_right, hindex]; decide)
    rw [relIndex_top_right, hindex, ← inf_relIndex_right, hd.eq_bot,
      relIndex_bot_left] at h
    exact h
  have hdvd : 3 ∣ Nat.card P := P.dvd_card_of_dvd_card (hindex ▸ S.index_dvd_card)
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)

end Subgroup
