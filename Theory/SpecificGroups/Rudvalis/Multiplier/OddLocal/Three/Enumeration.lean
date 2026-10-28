module

public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Three.Generators
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Three.Collection
import Mathlib.Tactic.Group

/-!
Algebraic collection adapted from `CFSG/Quasithin/MainConverse/SporadicLocal/Ru/FiveSubgroup/Enumeration.lean`.
The original remains available to its converse consumers. This lower-layer
copy supports the multiplier calculation without an upward dependency.

# Certified collection relations and distinct Rudvalis three-subgroup elements

The commutator `z = y⁻¹*x⁻¹*y*x` commutes with `x,y`, and all three third
powers are one. The abstract collection proof therefore covers the subgroup
by 27 forms. Evaluation at point 1 separates these forms and also shows
that the two generators do not commute. Every finite check uses Lean's kernel.

Source: ATLAS `RuG1-p4060B0`; GLS3, Table 5.3r, p.279 (3A row).
The untrusted discovery and regeneration scripts are retained in `source/`.
-/

namespace Rudvalis.Multiplier.OddLocal.ThreeCertificate
open Rudvalis Theory.GroupTheory ThreeCollection

set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public def generators : Fin 2 → Model := ![x, y]
@[expose] public def P : Subgroup Model := Subgroup.closure (Set.range generators)
@[expose] public def z : Model := y⁻¹ * x⁻¹ * y * x
@[expose] public def reps : Coordinates → Model := rep x y z

public theorem x_cube : x ^ 3 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem y_cube : y ^ 3 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem z_cube : z ^ 3 = 1 := by
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
  ThreeCollection.transitions x y z x_cube y_cube z_cube x_commute_z y_commute_z swap t j

@[expose] public def basePoint : Fin 4060 := 1
@[expose] public def point (t : Coordinates) : Fin 4060 := (![![![1, 803, 3386], ![2717, 2692, 2041], ![2687, 679, 2897]], ![![1924, 107, 2227], ![1717, 2583, 3289], ![2264, 1902, 3390]], ![![614, 397, 2743], ![2937, 1531, 2008], ![3511, 3080, 895]]]) t.1 t.2.1 t.2.2

public theorem reps_point : ∀ t, (modelSubgroup.subtype (reps t)) basePoint = point t := by
  rintro ⟨i, j, k⟩
  revert i j k
  apply OrderCertificate.allFin₃
  decide +kernel

public theorem point_injective : Function.Injective point := by decide +kernel

public theorem noncommute : x * y ≠ y * x := by
  intro h
  have hn : xMap (yMap 1) ≠ yMap (xMap 1) := by decide +kernel
  exact hn (congrArg (fun g : Model => (modelSubgroup.subtype g) 1) h)

end Rudvalis.Multiplier.OddLocal.ThreeCertificate
