module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry
public import Theory.Representation.GoldschmidtONan.OddReduction
public import Theory.Representation.GoldschmidtONan.OddTerminal

/-!
# Strong induction for the Goldschmidt–O’Nan theorem

Strong induction on the actual group cardinality supplies the precise
proper-subgroup hypothesis. The complete orbit geometry finishes three
alternatives; the remaining case gives odd order, then the fixed-line and
solvable terminal arguments give the exceptional dimensions and order.

The universal odd-order-solvability implication remains an explicit parameter
of this Theory theorem. The CFSG adapter supplies the proved Odd Order Theorem
without adding an upward import to Theory.

Source: GLS, Number 2, Chapter C, Proposition 14.2,
`refs/KGroup/GLS2/ChapterC.tex`, Steps 1–4 and the terminal argument.
-/

public section

namespace Representation.GoldschmidtONan

universe u v
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem alternatives_induction
    (hOdd : ∀ (H : Type u) [Group H] [Finite H], Odd (Nat.card H) → Group.IsSolvable H)
    (n : ℕ) :
    ∀ (X : Type u) [Group X] [Finite X], Nat.card X = n →
      ∀ (ρ : Representation (ZMod 2) X V) (Y : Subgroup X),
        Input ρ Y → Alternatives ρ Y := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ _ hcard ρ Y h
    have hIH : ProperSubgroupCases ρ := by
      intro H hH C hC
      have hlt : Nat.card H < Nat.card X := by
        have hpos : 0 < Nat.card H := Nat.card_pos
        have hi : 0 < H.index := Nat.card_pos
        have hne : H.index ≠ 1 := fun he => hH (H.index_eq_one.mp he)
        have hc := H.card_mul_index
        have hi2 : 2 ≤ H.index := by omega
        nlinarith
      exact ih (Nat.card H) (hcard ▸ hlt) H rfl (ρ.comp H.subtype) C hC
    rcases h.geometric_alternatives with hfirst | hsecond | hthird | hgeom
    · exact Or.inl hfirst
    · exact Or.inr (Or.inl hsecond)
    · exact Or.inr (Or.inr (Or.inl hthird))
    · have ho := OddReduction.odd_of_geometry h h.suborbitGeometry hgeom hIH
      let _ : Group.IsSolvable X := hOdd X ho
      exact Or.inr (Or.inr (Or.inr (h.exceptionalCase_of_solvable
        h.suborbitGeometry hgeom ho)))

theorem Input.alternatives_of_odd_order_solvable
    {X : Type u} [Group X] [Finite X]
    {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}
    (h : Input ρ Y)
    (hOdd : ∀ (H : Type u) [Group H] [Finite H], Odd (Nat.card H) → Group.IsSolvable H) :
    Alternatives ρ Y :=
  alternatives_induction hOdd (Nat.card X) X rfl ρ Y h

end Representation.GoldschmidtONan

