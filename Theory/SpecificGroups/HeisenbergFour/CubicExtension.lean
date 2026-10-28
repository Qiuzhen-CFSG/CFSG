module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Tactic.Ring

/-!
# The cubic extension of the Heisenberg group over GF(4)

The order-64 normal subgroup has coordinates (a,b,c), with cross term a*b'
in its central coordinate. A unit u acts as (u*a,u⁻¹*b,c). Over GF(4), the
unit group has order three and fixes the central four-group pointwise.
This is the concrete R⋊X model for the centralizer of the four-group E
in the w=2 geometry. Its identification with an ambient centralizer and
its cubic-pair geometry are separate mathematical obligations.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3, 46.14 and the proof of
47.6(1), pp.251,257–258,264.
-/

@[expose] public section
namespace HeisenbergFour

/-- Upper unitriangular three by three coordinates over a commutative ring. -/
@[ext] structure Heisenberg (F : Type*) where
  a : F
  b : F
  c : F
  deriving DecidableEq

namespace Heisenberg
variable {F : Type*} [CommRing F]
instance : Mul (Heisenberg F) := ⟨fun s t =>
  ⟨s.a + t.a, s.b + t.b, s.c + t.c + s.a * t.b⟩⟩
instance : One (Heisenberg F) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (Heisenberg F) := ⟨fun s => ⟨-s.a, -s.b, -s.c + s.a * s.b⟩⟩
instance : Group (Heisenberg F) where
  mul_assoc s t u := by
    apply Heisenberg.ext
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · change (s.c + t.c + s.a * t.b) + u.c + (s.a + t.a) * u.b =
        s.c + (t.c + u.c + t.a * u.b) + s.a * (t.b + u.b)
      ring
  one_mul s := by
    apply Heisenberg.ext
    · exact zero_add _
    · exact zero_add _
    · change 0 + s.c + 0 * s.b = s.c
      ring
  mul_one s := by
    apply Heisenberg.ext
    · exact add_zero _
    · exact add_zero _
    · change s.c + 0 + s.a * 0 = s.c
      ring
  inv_mul_cancel s := by
    apply Heisenberg.ext
    · exact neg_add_cancel _
    · exact neg_add_cancel _
    · change (-s.c + s.a * s.b) + s.c + (-s.a) * s.b = 0
      ring

def coordinates : Heisenberg F ≃ F × F × F where
  toFun s := (s.a, s.b, s.c)
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite F] : Finite (Heisenberg F) := Finite.of_equiv _ coordinates.symm

omit [CommRing F] in
theorem card [Finite F] : Nat.card (Heisenberg F) = Nat.card F ^ 3 := by
  rw [Nat.card_congr coordinates, Nat.card_prod, Nat.card_prod]
  ring

/-- The diagonal action fixes the third coordinate pointwise. -/
def scale (u : Fˣ) : MulAut (Heisenberg F) where
  toFun s := ⟨u * s.a, ↑u⁻¹ * s.b, s.c⟩
  invFun s := ⟨↑u⁻¹ * s.a, u * s.b, s.c⟩
  left_inv s := by
    apply Heisenberg.ext <;> dsimp <;> simp [← mul_assoc]
  right_inv s := by
    apply Heisenberg.ext <;> dsimp <;> simp [← mul_assoc]
  map_mul' s t := by
    apply Heisenberg.ext
    · exact mul_add _ _ _
    · exact mul_add _ _ _
    · change s.c + t.c + s.a * t.b = s.c + t.c + (↑u * s.a) * (↑u⁻¹ * t.b)
      congr 1
      rw [mul_mul_mul_comm]
      simp

/-- The literal action used in the semidirect product. -/
def action : Fˣ →* MulAut (Heisenberg F) where
  toFun := scale
  map_one' := by
    ext s <;> simp [scale]
  map_mul' u v := by
    ext s <;> simp [scale, mul_assoc, mul_left_comm]

@[simp] theorem action_apply (u : Fˣ) (s : Heisenberg F) :
    action u s = ⟨u * s.a, ↑u⁻¹ * s.b, s.c⟩ := rfl

end Heisenberg

abbrev Field := GaloisField 2 2
abbrev Model := Heisenberg Field ⋊[Heisenberg.action] Fieldˣ

theorem field_card : Nat.card Field = 4 := GaloisField.card 2 2 (by decide)
theorem normal_card : Nat.card (Heisenberg Field) = 64 := by
  norm_num [Heisenberg.card, field_card]
theorem complement_card : Nat.card Fieldˣ = 3 := by
  rw [Nat.card_units, field_card]

/-- The distinguished cubic subgroup is the actual right factor. -/
noncomputable def cubic : Subgroup Model := SemidirectProduct.inr.range

/-- The normal two-subgroup is the actual left factor. -/
noncomputable def radical : Subgroup Model := SemidirectProduct.inl.range

theorem cubic_card : Nat.card cubic = 3 := by
  let f : Fieldˣ →* Model := SemidirectProduct.inr
  exact (Nat.card_congr (MonoidHom.ofInjective (f := f)
    SemidirectProduct.inr_injective).toEquiv).symm.trans complement_card

end HeisenbergFour
