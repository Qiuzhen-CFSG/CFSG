module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Operations

/-! A finite list of proposed F₄ identities is checked by kernel reduction.
Soundness translates each successful check into its ordinary matrix identity. -/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed
open SmallModels.Arithmetic

inductive Check where
  | product (a b c : Mat)
  | inverse (a b : Mat)
  | add (a b c : Mat)
  | scale (c : Fin 4) (a b : Mat)
  | one (a : Mat)
  | outer (v lam : Row) (a : Mat)
  | transpose (a b : Mat)
  | trace (a : Mat) (c : Fin 4)
  | vecMul (v : Row) (a : Mat) (w : Row)

def Check.run (n : ℕ) : Check → Bool
  | .product a b c => checkProduct n a b c
  | .inverse a b => checkInverse n a b
  | .add a b c => checkAdd n a b c
  | .scale c a b => checkScale n c a b
  | .one a => checkOne n a
  | .outer v lam a => checkOuter n v lam a
  | .transpose a b => checkTranspose n a b
  | .trace a c => checkTrace n a c
  | .vecMul v a w => rowProduct v a n == w

variable {F : Type*} [Field F] [CharP F 2]

def Check.Holds (t : F) (n : ℕ) : Check → Prop
  | .product a b c => eval t n a * eval t n b = eval t n c
  | .inverse a b => eval t n a * eval t n b = 1
  | .add a b c => eval t n a + eval t n b = eval t n c
  | .scale c a b => coefficient t c • eval t n a = eval t n b
  | .one a => eval t n a = 1
  | .outer v lam a => eval t n a = Matrix.vecMulVec (evalVector t n v) (evalVector t n lam)
  | .transpose a b => (eval t n a).transpose = eval t n b
  | .trace a c => (eval t n a).trace = coefficient t c
  | .vecMul v a w => Matrix.vecMul (evalVector t n v) (eval t n a) = evalVector t n w

theorem Check.sound (t : F) (ht : t ^ 2 = t + 1) (n : ℕ) (c : Check)
    (h : c.run n = true) : c.Holds t n := by
  cases c with
  | product a b c => exact eval_product t ht n a b c h
  | inverse a b => exact eval_inverse t ht n a b h
  | add a b c => exact eval_add t n a b c h
  | scale c a b => exact eval_scale t ht n c a b h
  | one a => exact eval_one t n a h
  | outer v lam a => exact eval_outer t ht n v lam a h
  | transpose a b => exact eval_transpose t n a b h
  | trace a c => exact eval_trace t n a c h
  | vecMul v a w => exact eval_vecMul t ht n v a w (eq_of_beq h)

def checkList (n : ℕ) (cs : List Check) : Bool := cs.all (Check.run n)

theorem checkList_sound (t : F) (ht : t ^ 2 = t + 1) (n : ℕ) (cs : List Check)
    (h : checkList n cs = true) (i : ℕ) (hi : i < cs.length) : (cs[i]).Holds t n :=
  Check.sound t ht n _ (List.all_eq_true.mp h _ (List.getElem_mem hi))

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed
