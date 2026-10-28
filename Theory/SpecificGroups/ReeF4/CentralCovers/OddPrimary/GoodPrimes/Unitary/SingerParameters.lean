module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Field parameters for the full special-unitary Singer torus

For q = 2^(2m+1), the (q²−q+1)-st roots of unity in GF(q⁶) form a cyclic
parameter group of exactly that order. The factorizations of q³+1 and
q⁴+q²+1 show that multiplication by a parameter has unitary norm and
special-linear determinant norm one. These are the two scalar identities
for the trace Hermitian form Tr_{q⁶/q²}(x y^(q³)).

The actual three-dimensional matrix action, its Hermitian form and its
transport to the identity form remain separate construction obligations.
`Transfer.singer_subgroup_of_parameters` consumes that faithful action.
No projective quotient is taken: in particular q=8 gives order 57, not 19.

Sources: GLS3 §4.10 (finite tori), §6.5 and Theorem 6.5.3(c);
refs/KGroup/GLS3/chapter4.tex and chapter6.tex.
-/

@[expose] public noncomputable section

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.SingerParameters

abbrev Field (m : ℕ) : Type := GaloisField 2 ((2 * m + 1) * 6)

abbrev order (m : ℕ) : ℕ := (2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1

abbrev Group (m : ℕ) := rootsOfUnity (order m) (Field m)

theorem field_card (m : ℕ) : Nat.card (Field m) = (2 ^ (2 * m + 1)) ^ 6 := by
  rw [GaloisField.card 2 ((2 * m + 1) * 6) (by omega), pow_mul]

theorem cubic_factor (q : ℕ) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have hle : q ≤ q ^ 2 := by nlinarith
  have hs := congrArg (fun a : ℕ => (q + 1) * a) (Nat.sub_add_cancel hle)
  nlinarith

theorem norm_factor (q : ℕ) :
    q ^ 4 + q ^ 2 + 1 = (q ^ 2 + q + 1) * (q ^ 2 - q + 1) := by
  have hle : q ≤ q ^ 2 := by nlinarith
  have hs := congrArg (fun a : ℕ => (q ^ 2 + q + 1) * a) (Nat.sub_add_cancel hle)
  nlinarith

theorem order_dvd_field_units (m : ℕ) : order m ∣ Nat.card (Field m) - 1 := by
  rw [field_card, show (2 ^ (2 * m + 1)) ^ 6 = ((2 ^ (2 * m + 1)) ^ 3) ^ 2 by ring,
    show ((2 ^ (2 * m + 1)) ^ 3) ^ 2 - 1 =
      ((2 ^ (2 * m + 1)) ^ 3 - 1) * ((2 ^ (2 * m + 1)) ^ 3 + 1) by
        simpa [mul_comm] using Nat.sq_sub_sq ((2 ^ (2 * m + 1)) ^ 3) 1,
    cubic_factor]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

/-- The full Singer parameter group has order q²−q+1. -/
theorem card (m : ℕ) : Nat.card (Group m) = order m := by
  change Nat.card (rootsOfUnity (order m) (Field m)) = _
  rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_units]
  exact Nat.gcd_eq_right (order_dvd_field_units m)

/-- Literal cyclic coordinates on the sixth-degree field parameter group. -/
def equiv (m : ℕ) : Multiplicative (ZMod (order m)) ≃* Group m :=
  mulEquivOfCyclicCardEq (by change Nat.card (ZMod _) = _; rw [Nat.card_zmod, card])

private theorem pow_eq_one_of_order_dvd (m : ℕ) (a : Group m) {n : ℕ}
    (hn : order m ∣ n) : (a.val : Field m) ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have ha : (a.val : Field m) ^ order m = 1 :=
    (mem_rootsOfUnity' _ _).mp a.property
  rw [pow_mul, ha, one_pow]

/-- Multiplication by a parameter preserves the trace Hermitian form
Tr_{q⁶/q²}(x y^(q³)). -/
theorem unitary_norm (m : ℕ) (a : Group m) :
    (a.val : Field m) ^ ((2 ^ (2 * m + 1)) ^ 3 + 1) = 1 := by
  apply pow_eq_one_of_order_dvd
  rw [cubic_factor]
  exact dvd_mul_left _ _

/-- The determinant norm from q⁶ to q² is one on every parameter. -/
theorem determinant_norm (m : ℕ) (a : Group m) :
    (a.val : Field m) ^ ((2 ^ (2 * m + 1)) ^ 4 + (2 ^ (2 * m + 1)) ^ 2 + 1) = 1 := by
  apply pow_eq_one_of_order_dvd
  rw [norm_factor]
  exact dvd_mul_left _ _

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.SingerParameters
