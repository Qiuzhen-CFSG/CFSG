module
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder

/-!
# Order-seven actors on the small binary linear groups

The actual automorphism order divides q(q²−1)n. At n = 2, 4, or 8
this number is prime to seven, so every action of a group of order seven
on PSL₂(2ⁿ) is trivial. The action is arbitrary; no innerness or field
parameter comparison is assumed.

Source: the semilinear automorphism calculation in GLS3 §2.5 and the
order-seven obstruction in Aschbacher–Smith 5.2.2, printed p.648.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2.SmallDegreeSevenActors

/-- The automorphism groups at the three small binary degrees are seven-free. -/
theorem seven_not_dvd_card_aut {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : n = 2 ∨ n = 4 ∨ n = 8) :
    ¬ 7 ∣ Nat.card (MulAut PSL(2,F)) := by
  intro hd
  have hh := hd.trans (BinaryAutomorphismOrder.aut_card_dvd hF)
  rcases hn with rfl | rfl | rfl <;> norm_num at hh

/-- Every order-seven action on these actual matrix quotients is trivial. -/
theorem action_eq_one {A F : Type*} [Group A] [Finite A]
    [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : n = 2 ∨ n = 4 ∨ n = 8)
    (hc : Nat.card A = 7) (f : A →* MulAut PSL(2,F)) : f = 1 := by
  have hd := card_range_dvd f
  rw [hc] at hd
  rcases (by decide : Nat.Prime 7).eq_one_or_self_of_dvd _ hd with h1 | h7
  · have hb : f.range = ⊥ := f.range.eq_bot_of_card_eq h1
    apply MonoidHom.ext
    intro a
    exact mem_bot.mp (hb ▸ (show f a ∈ f.range from ⟨a,rfl⟩))
  · exact (seven_not_dvd_card_aut hF hn
      (h7 ▸ f.range.card_subgroup_dvd_card)).elim

end Theory.PSL2.SmallDegreeSevenActors
