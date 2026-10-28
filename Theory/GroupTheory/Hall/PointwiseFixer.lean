module
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.Hall.OddNormalProducts

/-!
# Pointwise odd Hall fixers modulo a normal Sylow two-subgroup

When the two-core has odd index, an odd Hall subgroup complements it. An
automorphism fixing that Hall subgroup therefore acts trivially on the
quotient by the two-core. This uses the actual Hall complement, without
replacing it by a conjugate.

Source: Aschbacher--Smith, the Hall-fixer argument in 14.2.12, printed p.983.
-/

public section
open Subgroup

namespace Subgroup.OddHall
variable {X : Type*} [Group X] [Finite X]

theorem fixed_mod_core_of_pointwise_hall
    (hc : Odd (pCore 2 X).index) (a : MulAut X) (D : Subgroup X)
    (hD : IsHallSubgroup oddPrimes D) (hfix : ∀ d ∈ D, a d = d) (x : X) :
    a x * x⁻¹ ∈ pCore 2 X := by
  let S : Sylow 2 X := pCore_isPGroup.toSylow hc.not_two_dvd_nat
  obtain ⟨⟨u,d⟩,he⟩ := (sylow_complement_of_hall S hD).2 x
  have hu : (u : X) ∈ pCore 2 X := u.property
  have hau : a u.val ∈ pCore 2 X := by
    rw [← pCore_map_iso 2 a]
    exact mem_map_of_mem _ hu
  rw [← he, map_mul, hfix d.val d.property, mul_inv_rev]
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right] using
    (pCore 2 X).mul_mem hau ((pCore 2 X).inv_mem hu)

end Subgroup.OddHall
