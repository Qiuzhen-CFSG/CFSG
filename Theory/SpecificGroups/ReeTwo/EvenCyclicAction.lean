module
public import Theory.SpecificGroups.ReeTwo.Sylow

/-!
# Collected multiplication for even cyclic coordinates

The square of the root-one action is a polynomial map on the core. Its
homomorphism law is a polynomial identity over the binary field; equality
with the original action is checked on the ten root generators. This gives
collected multiplication and powers when the cyclic-four coordinate is even.

Source: Shinoda (1975), (2.3), pp. 81–82, with the conventions and
multiplication verified in `Core`, `RootAction`, and `Sylow`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.EvenCyclicAction
set_option maxRecDepth 32768

def actionTwo (x : Core) : Core where
  b0 := x.b0
  b1 := x.b1
  b2 := x.b0 + x.b2
  b3 := x.b0 + x.b3
  b4 := x.b0 + x.b1 + x.b4
  b5 := x.b0 + x.b5
  b6 := x.b0 + x.b0 * x.b1 + x.b6
  b7 := x.b0 + x.b0 * x.b1 + x.b0 * x.b2 + x.b5 + x.b7
  b8 := x.b1 + x.b0 * x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b0 * x.b3 + x.b5 + x.b6 + x.b8
  b9 := x.b0 + x.b1 + x.b0 * x.b2 + x.b0 * x.b3 + x.b0 * x.b1 * x.b3 + x.b0 * x.b4 + x.b5 + x.b9

private theorem binary_sq : ∀ x : ZMod 2, x ^ 2 = x := by decide +kernel

set_option maxHeartbeats 4000000 in
def actionTwoHom : Core →* Core where
  toFun := actionTwo
  map_one' := by decide +kernel
  map_mul' x y := by
    change actionTwo (Core.mul x y) = Core.mul (actionTwo x) (actionTwo y)
    apply Core.ext
    all_goals simp only [actionTwo, Core.mul]
    all_goals ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [binary_sq]
    all_goals ring_nf
    all_goals reduce_mod_char

theorem actionTwo_eq (x : Core) : actionTwo x = Core.a (Core.a x) := by
  have h : actionTwoHom = Core.a.toMonoidHom.comp Core.a.toMonoidHom := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ j : CoreRoot,
      actionTwoHom (Core.root j) = (Core.a.toMonoidHom.comp Core.a.toMonoidHom) (Core.root j))
  exact DFunLike.congr_fun h x

def fastMul (x y : SylowModel) : SylowModel :=
  ⟨x.left * (if x.right = 1 then y.left else actionTwo y.left), x.right * y.right⟩

theorem fastMul_eq (x y : SylowModel)
    (hx : x.right = 1 ∨ x.right = Multiplicative.ofAdd (2 : ZMod 4)) :
    fastMul x y = x * y := by
  apply SemidirectProduct.ext
  · change x.left * _ = x.left * _
    apply congrArg (x.left * ·)
    rcases hx with hx | hx
    · simp only [hx, ite_true, map_one, MulAut.one_apply]
    · rw [hx, if_neg (by decide)]
      exact actionTwo_eq _
  · rfl

def fastPow (x : SylowModel) : ℕ → SylowModel
  | 0 => 1
  | n + 1 => fastMul x (fastPow x n)

theorem fastPow_eq (x : SylowModel)
    (hx : x.right = 1 ∨ x.right = Multiplicative.ofAdd (2 : ZMod 4)) (n : ℕ) :
    fastPow x n = x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fastPow, fastMul_eq _ _ hx, ih, pow_succ']



end ReeTwo.SylowModel.EvenCyclicAction
