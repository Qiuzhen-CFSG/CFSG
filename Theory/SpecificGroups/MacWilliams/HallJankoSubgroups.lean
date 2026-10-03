module

public import Theory.SpecificGroups.MacWilliams.HallJankoCoordinates
public import Theory.ElementaryAbelian.Basic

/-!
# The marked normal four in Hall–Janko coordinates

The last two normal-word bits form a normal elementary subgroup of order four.
The binary formulas certify closure, normality and exponent two directly. This
marks the subgroup used by the intrinsic candidate and fixed-point calculations.

Source: the presentation in `SylowPresentations`; MacWilliams, Trans. AMS 150
(1970), and Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, p.386.
-/

namespace MacWilliamsSylow.HallJankoCoordinates

set_option maxRecDepth 10000

/-- The subgroup on the last two presentation generators: codes 0, 32, 64, 96. -/
@[expose] public def four : Subgroup Code where
  carrier := {x | x.toFin.val % 32 = 0}
  one_mem' := by decide
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

public instance (x : Code) : Decidable (x ∈ four) :=
  inferInstanceAs (Decidable (x.toFin.val % 32 = 0))

/-- Membership in the marked four is a test on the five low bits. -/
public theorem mem_four (x : Code) : x ∈ four ↔ x.toFin.val % 32 = 0 := Iff.rfl

public instance four_normal : four.Normal where
  conj_mem := by decide +kernel

public instance four_elementary : IsElementaryAbelian 2 four where
  toIsMulCommutative := by
    apply isMulCommutative_iff.mpr
    decide +kernel
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    decide +kernel

/-- The marked normal elementary subgroup has order four. -/
public theorem four_card : Nat.card four = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end MacWilliamsSylow.HallJankoCoordinates
