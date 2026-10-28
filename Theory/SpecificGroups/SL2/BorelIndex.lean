module
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
public import BenderSuzuki.External.Huppert.II.theorem_6_14
/-!
# The index of the even-field matrix Borel

The exact orders q(q-1) and q(q²-1) give Borel index q+1, including q=2.
This is the branching factor in the linear local action used in DGS,
Groups and Graphs (1985), Part II, 6.7--6.8, p.123. The group order is
Huppert II.6.14; the Borel is the actual upper-root normalizer.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The actual matrix Borel has q+1 cosets over a finite field of characteristic two. -/
theorem rankOneBorel_index_even : (rankOneBorel F).index = Nat.card F + 1 := by
  have hc : Nat.card (rankOneBorel F) = Nat.card F * (Nat.card F - 1) :=
    card_sylow_normalizer_even (upperUnipotentSylow F 2)
  have hs := BenderSuzuki.External.huppert614_card_specialLinearGroup (K := F)
  have hcount := (rankOneBorel F).card_mul_index
  rw [hc, hs] at hcount
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hpos : 0 < Nat.card F * (Nat.card F - 1) := Nat.mul_pos (by omega) (by omega)
  have he : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ Nat.card F),
      Nat.sub_add_cancel (by nlinarith : 1 ≤ Nat.card F ^ 2)]
  rw [he, ←mul_assoc] at hcount
  exact Nat.eq_of_mul_eq_mul_left hpos hcount
end Matrix.SpecialLinearGroup
