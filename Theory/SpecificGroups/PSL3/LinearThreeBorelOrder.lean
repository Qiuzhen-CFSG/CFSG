module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# The order of a PSL₃(4) Borel

For any finite field of order four, the projective upper triangular subgroup has
order `4^3 · 3 = 192`.  The calculation is retained as a small interface for
central-cover arguments: it uses the actual unipotent/torus complement and the
cubic scalar quotient.

Source: Aschbacher–Smith, E.6.8(1), printed pp.247–250.
-/

public section

open Subgroup
open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
namespace Matrix.PSL3.CartanActions.BorelQuotient

variable (F : Type*) [Field F] [Finite F]

/-- The projective Borel over a field of order four has order `192`. -/
theorem card_borel_linear_three_four (hF : Nat.card F = 2 ^ 2) :
    Nat.card (borel F) = 192 := by
  have hcomp := (borel_complement F hF).card_mul_card
  have htor := card_torus_mul_scalar F
  have hu := card_unipotent F
  have hU' : Nat.card ((unipotent F).subgroupOf (borel F)) = Nat.card F ^ 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (unipotent_le_borel F)).toEquiv).trans hu
  have hT' : Nat.card ((torus F).subgroupOf (borel F)) = Nat.card (torus F) :=
    Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv
  rw [hU', hT'] at hcomp
  rw [hF] at hcomp
  rw [hF] at htor
  norm_num at hcomp htor ⊢
  omega

end Matrix.PSL3.CartanActions.BorelQuotient
