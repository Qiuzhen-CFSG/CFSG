module

public import Theory.SpecificGroups.ReeTwo.RootTwistedSylow

/-!
# Collected multiplication in the root-twisted extension

Explicit polynomial formulas for the four possible actor coordinates avoid
iterating the root-word action during finite certificates. The generator formula
is verified as a homomorphism and checked on the ten roots. The other formulas
follow by polynomial identities in characteristic two.

Source: Shinoda (1975), pp.81–83, via `Core` and `RootAction`; the generator
polynomial adapts the calculation in `TwistedParityPowerCounts` by the central
automorphism of `CoreRootTwist`.
-/

namespace ReeTwo.RootTwistedSylow

private def actionPolynomial (x : Core) : Core where
  b0 := x.b0
  b1 := x.b0 + x.b1
  b2 := x.b0 + x.b1 + x.b2
  b3 := x.b1 + x.b3
  b4 := x.b0 + x.b1 + x.b3 + x.b4
  b5 := x.b0 + x.b0 * x.b1 + x.b5
  b6 := x.b0 + x.b1 + x.b0 * x.b1 + x.b5 + x.b6
  b7 := x.b0 + x.b0 * x.b1 + x.b1 * x.b2 + x.b6 + x.b7
  b8 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b5 + x.b6 + x.b7 + x.b8
  b9 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b0 * x.b4 +
    x.b0 * x.b1 * x.b4 + x.b5 + x.b6 + x.b9 + x.b1 + x.b2 + x.b3

set_option maxHeartbeats 8000000 in
private def actionHom : Core →* Core where
  toFun := actionPolynomial
  map_one' := by decide +kernel
  map_mul' x y := by
    change actionPolynomial (Core.mul x y) = Core.mul (actionPolynomial x) (actionPolynomial y)
    apply Core.ext <;> simp only [actionPolynomial, Core.mul] <;> ring_nf
    all_goals reduce_mod_char
    all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

private theorem actionPolynomial_eq (x : Core) : actionPolynomial x = (Core.rootTwist * Core.a) x := by
  have h : actionHom = (Core.rootTwist * Core.a).toMonoidHom := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ i : CoreRoot,
      actionHom (Core.root i) = (Core.rootTwist * Core.a) (Core.root i))
  exact DFunLike.congr_fun h x

private def cyclicAction (t : FiveFour.Cyclic 4) (x : Core) : Core :=
  (actionPolynomial^[t.toAdd.val]) x

private theorem cyclicAction_eq (t : FiveFour.Cyclic 4) (x : Core) :
    cyclicAction t x = rootTwistedAction t x := by
  change (actionPolynomial^[t.toAdd.val]) x = ((Core.rootTwist * Core.a) ^ t.toAdd.val) x
  generalize t.toAdd.val = n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, actionPolynomial_eq, pow_succ]
    rfl

private def actionTwo (x : Core) : Core where
  b0 := x.b0
  b1 := x.b1
  b2 := x.b0 + x.b2
  b3 := x.b0 + x.b3
  b4 := x.b0 + x.b1 + x.b4
  b5 := x.b0 + x.b5
  b6 := x.b0 + x.b6 + x.b0 * x.b1
  b7 := x.b0 + x.b5 + x.b7 + x.b0 * x.b1 + x.b0 * x.b2
  b8 := x.b1 + x.b5 + x.b6 + x.b8 + x.b0 * x.b1 + x.b0 * x.b2 + x.b0 * x.b3 + x.b1 * x.b2
  b9 := x.b0 + x.b1 + x.b5 + x.b9 + x.b0 * x.b2 + x.b0 * x.b3 + x.b0 * x.b4 + x.b0 * x.b1 * x.b3

private def actionThree (x : Core) : Core where
  b0 := x.b0
  b1 := x.b0 + x.b1
  b2 := x.b1 + x.b2
  b3 := x.b0 + x.b1 + x.b3
  b4 := x.b0 + x.b3 + x.b4
  b5 := x.b5 + x.b0 * x.b1
  b6 := x.b0 + x.b1 + x.b5 + x.b6
  b7 := x.b0 + x.b5 + x.b6 + x.b7 + x.b0 * x.b2 + x.b1 * x.b2
  b8 := x.b0 + x.b5 + x.b7 + x.b8 + x.b0 * x.b1 + x.b0 * x.b2 + x.b0 * x.b3 + x.b1 * x.b3
  b9 := x.b1 + x.b2 + x.b3 + x.b6 + x.b9 + x.b0 * x.b3 + x.b1 * x.b2 + x.b1 * x.b3 + x.b0 * x.b1 * x.b3 + x.b0 * x.b1 * x.b4

private def closedAction (t : FiveFour.Cyclic 4) (x : Core) : Core :=
  if t.toAdd.val = 0 then x else if t.toAdd.val = 1 then actionPolynomial x
  else if t.toAdd.val = 2 then actionTwo x else actionThree x

set_option maxHeartbeats 8000000 in
private theorem actionTwo_eq (x : Core) : actionTwo x = actionPolynomial (actionPolynomial x) := by
  apply Core.ext <;> simp only [actionTwo, actionPolynomial] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide,
    show ∀ z : ZMod 2, z ^ 3 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

set_option maxHeartbeats 8000000 in
private theorem actionThree_eq (x : Core) : actionThree x = actionPolynomial (actionTwo x) := by
  apply Core.ext <;> simp only [actionThree, actionTwo, actionPolynomial] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

private theorem closedAction_eq (t : FiveFour.Cyclic 4) (x : Core) :
    closedAction t x = cyclicAction t x := by
  have hv := t.toAdd.val_lt
  unfold closedAction cyclicAction
  interval_cases t.toAdd.val <;> simp [Function.iterate_succ_apply', ← actionTwo_eq, ← actionThree_eq]

/-- Explicit collected action of each of the four actor elements. -/
@[expose] public def coordinateAction (t : FiveFour.Cyclic 4) (x : Core) : Core :=
  if t.toAdd.val = 0 then x else if t.toAdd.val = 1 then
    { b0 := x.b0
      b1 := x.b0 + x.b1
      b2 := x.b0 + x.b1 + x.b2
      b3 := x.b1 + x.b3
      b4 := x.b0 + x.b1 + x.b3 + x.b4
      b5 := x.b0 + x.b0 * x.b1 + x.b5
      b6 := x.b0 + x.b1 + x.b0 * x.b1 + x.b5 + x.b6
      b7 := x.b0 + x.b0 * x.b1 + x.b1 * x.b2 + x.b6 + x.b7
      b8 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b5 + x.b6 + x.b7 + x.b8
      b9 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b0 * x.b4 +
        x.b0 * x.b1 * x.b4 + x.b5 + x.b6 + x.b9 + x.b1 + x.b2 + x.b3 }
  else if t.toAdd.val = 2 then
    { b0 := x.b0
      b1 := x.b1
      b2 := x.b0 + x.b2
      b3 := x.b0 + x.b3
      b4 := x.b0 + x.b1 + x.b4
      b5 := x.b0 + x.b5
      b6 := x.b0 + x.b6 + x.b0 * x.b1
      b7 := x.b0 + x.b5 + x.b7 + x.b0 * x.b1 + x.b0 * x.b2
      b8 := x.b1 + x.b5 + x.b6 + x.b8 + x.b0 * x.b1 + x.b0 * x.b2 + x.b0 * x.b3 + x.b1 * x.b2
      b9 := x.b0 + x.b1 + x.b5 + x.b9 + x.b0 * x.b2 + x.b0 * x.b3 + x.b0 * x.b4 + x.b0 * x.b1 * x.b3 }
  else
    { b0 := x.b0
      b1 := x.b0 + x.b1
      b2 := x.b1 + x.b2
      b3 := x.b0 + x.b1 + x.b3
      b4 := x.b0 + x.b3 + x.b4
      b5 := x.b5 + x.b0 * x.b1
      b6 := x.b0 + x.b1 + x.b5 + x.b6
      b7 := x.b0 + x.b5 + x.b6 + x.b7 + x.b0 * x.b2 + x.b1 * x.b2
      b8 := x.b0 + x.b5 + x.b7 + x.b8 + x.b0 * x.b1 + x.b0 * x.b2 + x.b0 * x.b3 + x.b1 * x.b3
      b9 := x.b1 + x.b2 + x.b3 + x.b6 + x.b9 + x.b0 * x.b3 + x.b1 * x.b2 + x.b1 * x.b3 + x.b0 * x.b1 * x.b3 + x.b0 * x.b1 * x.b4 }

/-- The polynomial action is the original root-twisted action. -/
public theorem coordinateAction_eq (t : FiveFour.Cyclic 4) (x : Core) :
    coordinateAction t x = rootTwistedAction t x :=
  (closedAction_eq t x).trans (cyclicAction_eq t x)

/-- Collected multiplication, suitable for kernel-checked finite calculations. -/
@[expose] public def coordinateMul (x y : RootTwistedSylow) : RootTwistedSylow :=
  ⟨x.left * coordinateAction x.right y.left, x.right * y.right⟩

public theorem coordinateMul_eq_mul (x y : RootTwistedSylow) : coordinateMul x y = x * y := by
  apply SemidirectProduct.ext
  · exact congrArg (x.left * ·) (coordinateAction_eq x.right y.left)
  · rfl


end ReeTwo.RootTwistedSylow
