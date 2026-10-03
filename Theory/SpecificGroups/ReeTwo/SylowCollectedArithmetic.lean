module

public import Theory.SpecificGroups.ReeTwo.Sylow
public import Theory.GroupTheory.SubgroupClosureWords

/-!
# Collected arithmetic in the Ree two Sylow model

The polynomial root-one action is multiplicative and agrees with the existing
`Core.a` on the ten generating roots. Its iterates therefore give the original
semidirect-product action. The resulting multiplication, inverse, conjugation,
and word evaluator are proved equal to the original group operations.

These formulas shorten kernel reduction of finite word certificates. The action
polynomial follows the calculation in `TwistedParityPowerCounts`; the proof by
generators follows `ParityFrattiniPowerCounts`.

Source: Shinoda (1975), (2.3), pp. 81–82, and the root convention of `RootAction`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.Collected
open Theory.GroupTheory
def actionPolynomial (x : Core) : Core where
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
set_option maxRecDepth 8192 in
theorem actionPolynomial_eq (x : Core) : actionPolynomial x = Core.a x := by
  have h : actionHom = Core.a.toMonoidHom := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ i : CoreRoot, actionHom (Core.root i) = Core.a (Core.root i))
  exact DFunLike.congr_fun h x

def cyclicAction (t : FiveFour.Cyclic 4) (x : Core) : Core :=
  (actionPolynomial^[t.toAdd.val]) x

theorem cyclicAction_eq (t : FiveFour.Cyclic 4) (x : Core) :
    cyclicAction t x = Core.complementAction (SemidirectProduct.inr t) x := by
  change (actionPolynomial^[t.toAdd.val]) x = (Core.a ^ t.toAdd.val) x
  generalize t.toAdd.val = n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, actionPolynomial_eq, pow_succ]
    rfl

def collectedMul (x y : SylowModel) : SylowModel :=
  ⟨x.left * cyclicAction x.right y.left, x.right * y.right⟩

theorem collectedMul_eq (x y : SylowModel) : collectedMul x y = x * y := by
  apply SemidirectProduct.ext
  · exact congrArg (x.left * ·) (cyclicAction_eq x.right y.left)
  · rfl


def collectedInv (x : SylowModel) : SylowModel :=
  ⟨cyclicAction x.right⁻¹ x.left⁻¹, x.right⁻¹⟩
theorem collectedInv_eq (x : SylowModel) : collectedInv x = x⁻¹ := by
  apply SemidirectProduct.ext
  · exact cyclicAction_eq _ _
  · rfl

def collectedConj (g x : SylowModel) := collectedMul (collectedMul g x) (collectedInv g)
theorem collectedConj_eq (g x : SylowModel) : collectedConj g x = MulAut.conj g x := by
  simp only [collectedConj, collectedMul_eq, collectedInv_eq, MulAut.conj_apply]

def collectedEval {n : Nat} (a : Fin n → SylowModel) : List (Fin n) → SylowModel
  | [] => 1
  | k :: ks => collectedMul (a k) (collectedEval a ks)
theorem collectedEval_eq {n : Nat} (a : Fin n → SylowModel) (w : List (Fin n)) :
    collectedEval a w = evalWord a w := by
  induction w with
  | nil => rfl
  | cons k ks ih => simp only [collectedEval, collectedMul_eq, ih, evalWord]

end ReeTwo.SylowModel.Collected
