module

public import Theory.SpecificGroups.ReeTwo.Sylow

/-!
# Complement action on the core with two zero leading coordinates

On the subgroup with `b₀ = b₁ = 0`, the cyclic-four action is linear in
all eight remaining core coordinates. Its coefficients are polynomials in
the low and high complement bits. We check the action on binary root powers
and use the ordered normal form to extend it to arbitrary elements.

Source: Shinoda (1975), (2.3), pp. 81–82, as implemented in `Core`,
`RootAction`, and `Sylow`.
-/

namespace ReeTwo.Core
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Polynomial formula for the cyclic-four action when the first two coordinates vanish. -/
@[expose] public def zeroHeadAction (t : FiveFour.Cyclic 4) (x : Core) : Core :=
  let u : ZMod 2 := t.toAdd.val
  let v : ZMod 2 := (t.toAdd.val / 2 : ℕ)
  ⟨0, 0, x.b2, x.b3, x.b4 + u * x.b3, x.b5, x.b6 + u * x.b5,
    x.b7 + u * x.b6 + v * x.b5,
    x.b8 + u * x.b7 + (u + v) * x.b6 + (u + v + u * v) * x.b5,
    x.b9 + u * x.b6 + (u + v) * x.b5⟩

private theorem action_root_power : ∀ (t : FiveFour.Cyclic 4) (i : CoreRoot)
    (b : ZMod 2), 2 ≤ i.val →
    Core.complementAction (SemidirectProduct.inr t) (Core.root i ^ b.val) =
      zeroHeadAction t (Core.ofCoords (fun j => if j = i then b else 0)) := by
  decide +kernel

/-- The verified complement action agrees with its restricted polynomial formula. -/
public theorem complementAction_of_zero_head (t : FiveFour.Cyclic 4) (x : Core)
    (h0 : x.b0 = 0) (h1 : x.b1 = 0) :
    Core.complementAction (SemidirectProduct.inr t) x = zeroHeadAction t x := by
  conv_lhs => rw [← Core.normal_form x]
  simp only [h0, h1, ZMod.val_zero, pow_zero, one_mul, map_mul]
  rw [action_root_power t 2 x.b2 (by decide), action_root_power t 3 x.b3 (by decide),
    action_root_power t 4 x.b4 (by decide),
    action_root_power t 5 x.b5 (by decide), action_root_power t 6 x.b6 (by decide),
    action_root_power t 7 x.b7 (by decide),
    action_root_power t 8 x.b8 (by decide), action_root_power t 9 x.b9 (by decide)]
  change Core.mul (Core.mul (Core.mul (Core.mul (Core.mul (Core.mul (Core.mul _ _) _) _) _) _) _) _ = _
  apply Core.ext <;> simp [Core.mul, zeroHeadAction, Core.ofCoords] <;> ring

end ReeTwo.Core
