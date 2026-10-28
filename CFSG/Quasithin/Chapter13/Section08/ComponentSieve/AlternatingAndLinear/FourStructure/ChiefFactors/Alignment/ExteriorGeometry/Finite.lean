module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fin.VecNotation

/-!
# The finite exterior-plane calculation

In six binary coordinates ordered 01, 02, 03, 12, 13, 23, the eight maps below
are the exterior actions of E₀₁, E₁₀, E₂₃, E₃₂, E₀₂, E₀₃, E₁₂, E₁₃.
No set {0, x, y, x+y} with distinct nonzero x and y is stable under them.
The finite assertion is proved by kernel reduction. The importing geometry
module proves its correspondence with the genuine exterior square.

Source: the plane-stabilizer calculation used in Aschbacher–Smith 13.8.25,
printed p.960 (PDF p.977).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.ExteriorGeometry

abbrev Six := Fin 6 → ZMod 2
def step (i : Fin 8) (x : Six) : Six :=
  (![ ![x 0, x 1 + x 3, x 2 + x 4, x 3, x 4, x 5],
      ![x 0, x 1, x 2, x 3 + x 1, x 4 + x 2, x 5],
      ![x 0, x 1 + x 2, x 2, x 3 + x 4, x 4, x 5],
      ![x 0, x 1, x 2 + x 1, x 3, x 4 + x 3, x 5],
      ![x 0 + x 3, x 1, x 2 + x 5, x 3, x 4, x 5],
      ![x 0 + x 4, x 1 + x 5, x 2, x 3, x 4, x 5],
      ![x 0 + x 1, x 1, x 2, x 3, x 4 + x 5, x 5],
      ![x 0 + x 2, x 1, x 2, x 3 + x 5, x 4, x 5]] : Fin 8 → Six) i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_check : ∀ x y : Six, x ≠ 0 → y ≠ 0 → x ≠ y →
    ¬ (∀ i : Fin 8,
      (step i x = 0 ∨ step i x = x ∨ step i x = y ∨ step i x = x + y) ∧
      (step i y = 0 ∨ step i y = x ∨ step i y = y ∨ step i y = x + y)) := by
  decide +kernel

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.ExteriorGeometry
