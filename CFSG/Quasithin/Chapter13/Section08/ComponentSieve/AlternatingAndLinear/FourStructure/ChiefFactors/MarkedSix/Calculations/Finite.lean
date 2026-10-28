module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi

/-!
# Finite bounds for the exterior action of a plane radical

The four parameters describe the upper-right block of a unipotent binary
four-by-four matrix. The six coordinates are the minors 01, 02, 03, 12, 13,
23. The determinant polar form is `pairing`. Independent parameter vectors
have four common perpendicular vectors; their exterior operators have at
most eight common fixed vectors. A nonzero parameter fixes at most sixteen.

All three counts are verified by kernel reduction. The importing calculation
proves the identification with the actual exterior power and the radical.

Source: the intrinsic model calculation used in Aschbacher–Smith 13.8.25,
printed p.961, in place of the deleted-permutation catalogue B.3.2(6).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix.Calculations
abbrev Four := Fin 4 → ZMod 2
abbrev Six := Fin 6 → ZMod 2

def step (a : Four) (x : Six) : Six :=
  ![x 0 + a 2 * x 1 + a 3 * x 2 + a 0 * x 3 + a 1 * x 4 +
      (a 0 * a 3 + a 1 * a 2) * x 5,
    x 1 + a 1 * x 5, x 2 + a 0 * x 5,
    x 3 + a 3 * x 5, x 4 + a 2 * x 5, x 5]

def pairing (a b : Four) : ZMod 2 :=
  a 2 * b 1 + a 3 * b 0 + a 0 * b 3 + a 1 * b 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem perp_card : ∀ a b : Four, a ≠ 0 → b ≠ 0 → a ≠ b →
    Fintype.card {c : Four // pairing a c = 0 ∧ pairing b c = 0} = 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fixed_card : ∀ a : Four, a ≠ 0 →
    Fintype.card {x : Six // step a x = x} ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem common_fixed_card : ∀ a b : Four, a ≠ 0 → b ≠ 0 → a ≠ b →
    Fintype.card {x : Six // step a x = x ∧ step b x = x} ≤ 8 := by
  decide +kernel
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix.Calculations
