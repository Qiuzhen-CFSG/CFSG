module

public import Theory.SpecificGroups.ReeTwo.CoreRootConjugacy
public import Theory.SpecificGroups.ReeTwo.RootAction

/-!
# The central twist exchanging the two middle-root classes

Adding `b1 + b2 + b3` to the last coordinate is an involutory core
automorphism. It inverts the middle root and commutes with both specified
complement generators. Thus twisting the four-element generator retains
its square and its action on the five-element subgroup, while reversing
the middle-root orientation. Distinguishing these extensions requires
information from the neighboring parabolic.

Source: direct calculation in Shinoda's verified core coordinates, (2.3),
pp.81–82. This module asserts no identification of an actual local action.
-/

@[expose] public section
namespace ReeTwo.Core

/-- The central change of sign on the middle root. -/
def rootTwist : MulAut Core where
  toFun x := { x with b9 := x.b9 + x.b1 + x.b2 + x.b3 }
  invFun x := { x with b9 := x.b9 + x.b1 + x.b2 + x.b3 }
  left_inv x := by
    apply Core.ext <;> try rfl
    dsimp
    ring_nf
    reduce_mod_char
  right_inv x := by
    apply Core.ext <;> try rfl
    dsimp
    ring_nf
    reduce_mod_char
  map_mul' x y := by
    change { mul x y with b9 := (mul x y).b9 + (mul x y).b1 +
      (mul x y).b2 + (mul x y).b3 } =
      mul { x with b9 := x.b9 + x.b1 + x.b2 + x.b3 }
        { y with b9 := y.b9 + y.b1 + y.b2 + y.b3 }
    apply Core.ext <;> simp only [mul]
    ring

@[simp] theorem rootTwist_two : rootTwist ^ 2 = 1 := by
  apply aut_ext
  exact (by decide +kernel : ∀ i : CoreRoot, (rootTwist ^ 2) (root i) = root i)

@[simp] theorem rootTwist_root_two : rootTwist (root 2) = (root 2)⁻¹ := by
  decide +kernel

@[simp] theorem rootTwist_root_nine : rootTwist (root 9) = root 9 := by
  decide +kernel

/-- The central twist commutes with the specified order-four action. -/
theorem rootTwist_commute_a : Commute rootTwist a := by
  apply aut_ext
  exact (by decide +kernel : ∀ i : CoreRoot,
    (rootTwist * a) (root i) = (a * rootTwist) (root i))

/-- It also commutes with the specified Weyl action. -/
theorem rootTwist_commute_r : Commute rootTwist r := by
  apply aut_ext
  exact (by decide +kernel : ∀ i : CoreRoot,
    (rootTwist * r) (root i) = (r * rootTwist) (root i))

/-- In particular the five-element action is unchanged by this twist. -/
theorem rootTwist_commute_c : Commute rootTwist c :=
  (rootTwist_commute_a.pow_right 2).mul_right rootTwist_commute_r

/-- The two choices of order-four action have the same square. -/
theorem rootTwist_a_square : (rootTwist * a) ^ 2 = a ^ 2 := by
  rw [rootTwist_commute_a.mul_pow, rootTwist_two, _root_.one_mul]

theorem rootTwist_a_four : (rootTwist * a) ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, rootTwist_a_square, ← pow_mul]
  exact a_four

/-- The twisted action exchanges the middle-root classes. -/
theorem rootTwist_a_root_two : (rootTwist * a) (root 2) = (root 2)⁻¹ := by
  decide +kernel

/-- The Frobenius relation alone does not determine the orientation. -/
theorem rootTwist_a_conj_c :
    (rootTwist * a) * c * (rootTwist * a)⁻¹ = c ^ 2 := by
  calc
    (rootTwist * a) * c * (rootTwist * a)⁻¹ =
        rootTwist * (a * c * a⁻¹) * rootTwist⁻¹ := by group
    _ = rootTwist * c ^ 2 * rootTwist⁻¹ := by rw [a_conj_c]
    _ = c ^ 2 := by rw [(rootTwist_commute_c.pow_right 2).eq, mul_inv_cancel_right]

end ReeTwo.Core
