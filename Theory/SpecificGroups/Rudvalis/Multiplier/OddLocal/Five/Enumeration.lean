module

public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Five.Generators
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Five.Collection
import Mathlib.Tactic.Group

/-!
Adapted without changing the words or certificates from `CFSG/Quasithin/MainConverse/SporadicLocal/Ru/FiveSubgroup/Enumeration.lean`.
The original remains available to its converse consumers. This lower-layer
copy supports the multiplier calculation without an upward dependency.

# Certified collection relations and distinct Rudvalis five-subgroup elements

The commutator `z = y⁻¹*x⁻¹*y*x` commutes with `x,y`, and all three fifth
powers are one. The abstract collection proof therefore covers the subgroup
by 125 forms. Evaluation at point 0 separates these forms and also shows
that the two generators do not commute. Every finite check uses Lean's kernel.

Source: ATLAS `RuG1-p4060B0`; GLS3, Table 5.3r, p.279 (5A row).
The untrusted discovery and regeneration scripts are retained in `source/`.
-/

namespace Rudvalis.Multiplier.OddLocal.FiveCertificate
open Rudvalis Theory.GroupTheory FiveCollection

set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public def generators : Fin 2 → Model := ![x, y]
@[expose] public def P : Subgroup Model := Subgroup.closure (Set.range generators)
@[expose] public def z : Model := y⁻¹ * x⁻¹ * y * x
@[expose] public def reps : Coordinates → Model := rep x y z

public theorem x_fifth : x ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem y_fifth : y ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem z_fifth : z ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem x_commute_z : Commute x z := by
  change x * z = z * x
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem y_commute_z : Commute y z := by
  change y * z = z * y
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem swap : y * x = x * y * z := by
  dsimp [z]
  group

public theorem transitions (t : Coordinates) (j : Fin 2) :
    reps t * generators j = reps (next t j) :=
  FiveCollection.transitions x y z x_fifth y_fifth z_fifth x_commute_z y_commute_z swap t j

@[expose] public def basePoint : Fin 4060 := 0
@[expose] public def point (t : Coordinates) : Fin 4060 := ![![![0, 2783, 2938, 2085, 2815], ![1819, 867, 2021, 814, 2185], ![336, 2358, 1611, 3325, 3514], ![593, 37, 1125, 610, 1373], ![2790, 3965, 56, 2035, 2410]], ![![3866, 2446, 2913, 3177, 3701], ![1940, 337, 3032, 2777, 2392], ![962, 3688, 2407, 1964, 552], ![2557, 1217, 30, 3498, 4028], ![3770, 2319, 312, 352, 3877]], ![![4025, 3660, 1976, 2037, 2957], ![1369, 3422, 3375, 3753, 650], ![436, 2645, 1826, 3469, 1996], ![2043, 997, 3034, 967, 1515], ![340, 1517, 1753, 3745, 984]], ![![3398, 1168, 2334, 2534, 2756], ![3346, 2708, 2033, 708, 3207], ![256, 3405, 1181, 1079, 1625], ![1061, 1974, 1903, 2725, 406], ![1216, 1461, 310, 3354, 2690]], ![![2296, 1776, 2445, 2652, 3625], ![2520, 1043, 2241, 1793, 824], ![1528, 1937, 1642, 3911, 1733], ![915, 245, 232, 3386, 2170], ![1016, 249, 1732, 79, 1115]]] t.1 t.2.1 t.2.2

public theorem reps_point : ∀ t, (modelSubgroup.subtype (reps t)) basePoint = point t := by
  rintro ⟨i, j, k⟩
  revert i j k
  apply OrderCertificate.allFin₃
  decide +kernel

public theorem point_injective : Function.Injective point := by decide +kernel

public theorem noncommute : x * y ≠ y * x := by
  intro h
  have hn : xMap (yMap basePoint) ≠ yMap (xMap basePoint) := by decide +kernel
  exact hn (congrArg (fun g : Model => (modelSubgroup.subtype g) basePoint) h)

end Rudvalis.Multiplier.OddLocal.FiveCertificate
