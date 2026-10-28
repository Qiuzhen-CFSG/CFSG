module

public import Theory.SpecificGroups.ReeTwo.TwistedParityCoordinates

/-!
# Power fibers of the twisted Ree two parity coordinates

The cyclic-four coordinate and the nine free binary core coordinates parametrize
all 2,048 elements of the twisted parity kernel. We transport each power fiber
along this equivalence and count the resulting finite subtype. The certificates
for the square and fourth-power counts are checked by the Lean kernel.

To keep the enumeration tractable, we first verify a collected polynomial form
of the root-one action against `Core.a`. Iterating this action gives exactly the
existing semidirect-product multiplication, so the finite counts use the power
equations of the original group. No identification of the Frattini subgroup is
needed here.

Source: Shinoda (1975), (2.3), pp. 81–82, with the root conventions and
multiplication verified in `Core` and `RootAction`.
-/

namespace ReeTwo.SylowModel

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
    x.b0 * x.b1 * x.b4 + x.b5 + x.b6 + x.b9

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem actionPolynomial_eq : ∀ x : Core, actionPolynomial x = Core.a x := by decide +kernel

private def cyclicAction (t : FiveFour.Cyclic 4) (x : Core) : Core :=
  (actionPolynomial^[t.toAdd.val]) x

private theorem cyclicAction_eq (t : FiveFour.Cyclic 4) (x : Core) :
    cyclicAction t x = Core.complementAction (SemidirectProduct.inr t) x := by
  change (actionPolynomial^[t.toAdd.val]) x = (Core.a ^ t.toAdd.val) x
  generalize t.toAdd.val = n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, actionPolynomial_eq, pow_succ]
    rfl

private def collectedMul (x y : SylowModel) : SylowModel :=
  ⟨x.left * cyclicAction x.right y.left, x.right * y.right⟩

private theorem collectedMul_eq (x y : SylowModel) : collectedMul x y = x * y := by
  apply SemidirectProduct.ext
  · exact congrArg (x.left * ·) (cyclicAction_eq x.right y.left)
  · rfl

private def collectedPow (x : SylowModel) : ℕ → SylowModel
  | 0 => 1
  | n + 1 => collectedMul (collectedPow x n) x

private theorem collectedPow_eq (x : SylowModel) (n : ℕ) : collectedPow x n = x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [collectedPow, collectedMul_eq, ih, pow_succ]

private abbrev PowerParameters := FiveFour.Cyclic 4 × (Fin 9 → ZMod 2)

private def parameterFiber (v : TwistedParityQuotient) (n : ℕ) (p : PowerParameters) : Prop :=
  twistedParityCoordinates (twistedParityParameterEquiv.symm p) = v ∧
    collectedPow (twistedParityParameterEquiv.symm p).val n = 1

private instance (v : TwistedParityQuotient) (n : ℕ) :
    DecidablePred (parameterFiber v n) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

private def parameterFiberCard (v : TwistedParityQuotient) (n : ℕ) : ℕ :=
  Fintype.card {p : PowerParameters // parameterFiber v n p}

private theorem powerFiberCard_eq (v : TwistedParityQuotient) (n : ℕ) :
    twistedParityCoordinates.powerFiberCard v n = parameterFiberCard v n := by
  unfold MonoidHom.powerFiberCard parameterFiberCard
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine twistedParityParameterEquiv.subtypeEquiv ?_
  intro g
  simp only [parameterFiber, Equiv.symm_apply_apply, collectedPow_eq]
  exact and_congr_right (fun _ => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem count_certificate : ∀ v,
    (parameterFiberCard v 2, parameterFiberCard v 4) = twistedParityProfile v := by
  decide +kernel

/-- Square and fourth-power solution counts in every twisted coordinate fiber. -/
public theorem twistedParityCoordinates_powerFiberCard : ∀ v,
    (twistedParityCoordinates.powerFiberCard v 2,
      twistedParityCoordinates.powerFiberCard v 4) = twistedParityProfile v := by
  intro v
  rw [powerFiberCard_eq, powerFiberCard_eq]
  exact count_certificate v

end ReeTwo.SylowModel
