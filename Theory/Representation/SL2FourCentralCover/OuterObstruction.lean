module

public import Theory.Representation.SL2FourCentralCover.Coordinates

/-!
# The field involution cannot fix the full central line of the SL₂(4) cover

On the natural plane, the field involution squares coordinates and conjugates
the upper element of parameter `t` to that of parameter `t²`. Every compatible
binary linear lift to the six-dimensional universal SL₂(4) cover must square
its central F₄-line too. In particular it cannot fix that line pointwise.

The proof expresses a central vector as the sum of two root displacements.
It uses the literal cover projection and actual SL₂(4) root operators.

This is a boundary check for Aschbacher--Smith I.2.3, printed p.413: the
universal cover for `L` must not automatically be called a central cover for
an overgroup containing the field involution. It does not alone give a
counterexample to every interpretation of the printed ambient statement.
-/

public section
noncomputable section

namespace Representation.SL2FourCentralCover
open SL2FourNatural

/-- A lift of the field involution with its prescribed root conjugation cannot
fix the entire kernel of the universal SL₂(4) cover pointwise. -/
theorem no_pointwise_central_frobenius_lift
    (f : Space →ₗ[ZMod 2] Space)
    (hquot : ∀ w i, projection (f w) i = (projection w i) ^ 2)
    (hroot : ∀ t w, f (binaryAction (upper t) w) =
      binaryAction (upper (t ^ 2)) (f w))
    (hcentral : ∀ w, projection w = 0 → f w = w) : False := by
  let a : F := ⟨0, 1⟩
  have ha : a + a ^ 2 = 1 := by decide +kernel
  have ha4 : a ^ 4 = a := pow_four a
  have ha2 : a ^ 2 ≠ a := by decide +kernel
  let x : Space := coordinates.symm (0, ![0, a ^ 2])
  let y : Space := coordinates.symm (0, ![0, a])
  let z : Space := coordinates.symm (a, 0)
  have hz : projection z = 0 := by
    change (coordinates z).2 = 0
    simp only [z, coordinates.apply_symm_apply]
  have hsum : z = (binaryAction (upper 1) x - x) +
      (binaryAction (upper a) y - y) := by
    apply coordinates.injective
    rw [map_add, coordinates_upper_displacement, coordinates_upper_displacement]
    simp only [x, y, z, coordinates.apply_symm_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, one_pow, one_mul]
    apply Prod.ext
    · change a = a ^ 2 + a ^ 2 * a
      calc
        a = (a + a ^ 2) * a := by rw [ha, one_mul]
        _ = _ := by ring
    · change (0 : V) = ![a ^ 2, 0] + ![a * a, 0]
      funext i
      fin_cases i <;> simp [pow_two, CharTwo.add_self_eq_zero]
  have hf := congrArg f hsum
  rw [hcentral z hz, map_add, map_sub, map_sub, hroot, hroot] at hf
  have hc := congrArg (fun w => (coordinates w).1) hf
  rw [map_add, coordinates_upper_displacement, coordinates_upper_displacement] at hc
  have hx : (coordinates (f x)).2 1 = a ^ 4 := by
    change projection (f x) 1 = _
    rw [hquot]
    change ((coordinates x).2 1) ^ 2 = _
    simp only [x, coordinates.apply_symm_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  have hy : (coordinates (f y)).2 1 = a ^ 2 := by
    change projection (f y) 1 = _
    rw [hquot]
    change ((coordinates y).2 1) ^ 2 = _
    simp only [y, coordinates.apply_symm_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
  simp only [z, coordinates.apply_symm_apply, Prod.fst_add, hx, hy, one_pow,
    one_mul] at hc
  have he : a = a ^ 2 := by
    calc
      a = a ^ 4 + (a ^ 2) ^ 2 * a ^ 2 := hc
      _ = a ^ 2 * (a + a ^ 2) := by
        calc
          _ = a ^ 4 + a ^ 3 := by rw [← pow_mul, ha4]; ring
          _ = _ := by ring
      _ = a ^ 2 := by rw [ha, mul_one]
  exact ha2 he.symm

end Representation.SL2FourCentralCover
