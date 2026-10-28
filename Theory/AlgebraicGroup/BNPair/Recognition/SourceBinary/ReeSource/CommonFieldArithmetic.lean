module
import Mathlib.Data.Nat.GCD.Basic

/-!
# Arithmetic end of the Fong--Seitz common-field argument

The source action argument in I (6H)(a), p.51, produces the two divisibilities
`2^a - 1 ∣ 2^b - 1` and `2^b - 1 ∣ 2^a - 1`. This leaf records the exact
arithmetic conclusion separately from those group-action premises. It keeps
the source construction honest: the divisibilities must still be supplied by
the opposite-root Fitting actions, while their exponent consequence is fully
checked here.
-/

@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

theorem common_field_exponent_of_mutual_dvd {a b : ℕ}
    (_ha : 0 < a) (_hb : 0 < b)
    (hab : 2^a - 1 ∣ 2^b - 1)
    (hba : 2^b - 1 ∣ 2^a - 1) : a = b := by
  have hg : Nat.gcd (2^a - 1) (2^b - 1) = 2^a - 1 :=
    Nat.gcd_eq_left hab
  have hg' : Nat.gcd (2^a - 1) (2^b - 1) = 2^b - 1 := by
    rw [Nat.gcd_eq_right hba]
  have he : 2^a - 1 = 2^b - 1 := hg.symm.trans hg'
  apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
  have hpa : 0 < 2^a := Nat.pow_pos (by decide : 0 < (2 : ℕ))
  have hpb : 0 < 2^b := Nat.pow_pos (by decide : 0 < (2 : ℕ))
  exact Nat.sub_one_cancel hpa hpb he

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
