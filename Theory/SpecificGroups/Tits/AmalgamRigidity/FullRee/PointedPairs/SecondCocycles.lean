module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondArithmetic
/-!
# Six binary parameters for the second Weyl cocycles

The cyclic-four projection of the cocycle equation determines that coordinate
from the first and fifth core coordinates. Three collected component equations
then identify the paired coordinates and determine the last root. Thus every
cocycle has exactly the six-parameter form used by the explicit conjugator in
`SecondCensus`. The component checks use the verified collected multiplication;
the final argument is an equality in the original Sylow group.

Source: Shinoda's binary Ree collected roots (1975), pp.81--83, in the
pointed local calculation for Aschbacher--Smith F.4.8, printed p.278.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo SecondExtension SylowModel.Collected


private theorem binary_cases (a : ZMod 2) : a=0 ∨ a=1 :=
  (by decide : ∀ z : ZMod 2, z=0 ∨ z=1) a

private def normalizedInput (a b c d e f g h i : ZMod 2) : SylowModel :=
  ⟨⟨0,a,b,c,d,e,f,g,h,i⟩,
      Multiplicative.ofAdd ((a.val : ZMod 4)+2*(e.val : ZMod 4))⟩

private theorem product_b2_reduce (a b c d e f g h i : ZMod 2) :
    (collectedMul (normalizedInput a b c d e f g h i)
      (secondWeylPolynomial (normalizedInput a b c d e f g h i))).left.b2 =
    (collectedMul (normalizedInput a b c 0 e 0 0 0 0)
      (secondWeylPolynomial (normalizedInput a b c 0 e 0 0 0 0))).left.b2 := by
  rcases binary_cases a with rfl | rfl <;> rcases binary_cases e with rfl | rfl <;> rfl

private theorem product_b2 (a b c d e f g h i : ZMod 2) :
    ((normalizedInput a b c d e f g h i) *
      secondWeylPolynomial (normalizedInput a b c d e f g h i)).left.b2 = b+c := by
  rw [← collectedMul_eq, product_b2_reduce]
  exact (by decide +kernel : ∀ a b c e : ZMod 2,
    (collectedMul (normalizedInput a b c 0 e 0 0 0 0)
      (secondWeylPolynomial (normalizedInput a b c 0 e 0 0 0 0))).left.b2 = b+c) a b c e

private theorem product_b4 (a b d e f g h i : ZMod 2) :
    ((normalizedInput a b b d e f g h i) *
      secondWeylPolynomial (normalizedInput a b b d e f g h i)).left.b4 = d+f := by
  rw [← collectedMul_eq]
  exact (by decide +kernel : ∀ a b d e f g h i : ZMod 2,
    (collectedMul (normalizedInput a b b d e f g h i)
      (secondWeylPolynomial (normalizedInput a b b d e f g h i))).left.b4 = d+f) a b d e f g h i

private theorem product_b8 (a b d e g h i : ZMod 2) :
    ((normalizedInput a b b d e d g h i) *
      secondWeylPolynomial (normalizedInput a b b d e d g h i)).left.b8 = b+b*d+d*e+h+i := by
  rw [← collectedMul_eq]
  exact (by decide +kernel : ∀ a b d e g h i : ZMod 2,
    (collectedMul (normalizedInput a b b d e d g h i)
      (secondWeylPolynomial (normalizedInput a b b d e d g h i))).left.b8 = b+b*d+d*e+h+i) a b d e g h i

theorem polynomial_cocycle_right (x : SylowModel)
    (h : x * secondWeylPolynomial x = 1) :
    x.right = Multiplicative.ofAdd ((x.left.b1.val : ZMod 4)+2*(x.left.b5.val : ZMod 4)) := by
  have hh := congrArg (fun v : SylowModel => v.right.toAdd) h
  change x.right.toAdd + (-(x.left.b1.val : ZMod 4)+2*(x.left.b5.val : ZMod 4)) = 0 at hh
  have he : x.right.toAdd = (x.left.b1.val : ZMod 4)+2*(x.left.b5.val : ZMod 4) := by
    calc
      x.right.toAdd = -(-(x.left.b1.val : ZMod 4)+2*(x.left.b5.val : ZMod 4)) :=
        eq_neg_of_add_eq_zero_left hh
      _ = _ := (by decide : ∀ a b : ZMod 2,
        -(-(a.val : ZMod 4)+2*(b.val : ZMod 4)) =
        (a.val : ZMod 4)+2*(b.val : ZMod 4)) x.left.b1 x.left.b5
  exact congrArg Multiplicative.ofAdd he

theorem polynomial_cocycle_form (x : SylowModel) (hx0 : x.left.b0=0)
    (h : x * secondWeylPolynomial x = 1) :
    x = ⟨⟨0,x.left.b1,x.left.b2,x.left.b2,x.left.b4,x.left.b5,x.left.b4,
      x.left.b7,x.left.b8,x.left.b2+x.left.b2*x.left.b4+x.left.b4*x.left.b5+x.left.b8⟩,
      Multiplicative.ofAdd ((x.left.b1.val : ZMod 4)+2*(x.left.b5.val : ZMod 4))⟩ := by
  have hr := polynomial_cocycle_right x h
  have hx : x = normalizedInput x.left.b1 x.left.b2 x.left.b3 x.left.b4 x.left.b5
      x.left.b6 x.left.b7 x.left.b8 x.left.b9 := by
    apply SemidirectProduct.ext
    · apply Core.ext <;> first | exact hx0 | rfl
    · exact hr
  have h3 : x.left.b3=x.left.b2 := by
    have he : x.left.b2+x.left.b3=0 := by
      rw [← product_b2]
      change ((normalizedInput x.left.b1 x.left.b2 x.left.b3 x.left.b4 x.left.b5
        x.left.b6 x.left.b7 x.left.b8 x.left.b9) * _).left.b2=0
      rw [← hx, h]
      rfl
    simpa only [ZMod.neg_eq_self_mod_two] using (eq_neg_of_add_eq_zero_right he)
  have hx' : x = normalizedInput x.left.b1 x.left.b2 x.left.b2 x.left.b4 x.left.b5
      x.left.b6 x.left.b7 x.left.b8 x.left.b9 := by simpa only [h3] using hx
  have h6 : x.left.b6=x.left.b4 := by
    have he : x.left.b4+x.left.b6=0 := by
      rw [← product_b4]
      change ((normalizedInput x.left.b1 x.left.b2 x.left.b2 x.left.b4 x.left.b5
        x.left.b6 x.left.b7 x.left.b8 x.left.b9) * _).left.b4=0
      rw [← hx', h]
      rfl
    simpa only [ZMod.neg_eq_self_mod_two] using (eq_neg_of_add_eq_zero_right he)
  have hx'' : x = normalizedInput x.left.b1 x.left.b2 x.left.b2 x.left.b4 x.left.b5
      x.left.b4 x.left.b7 x.left.b8 x.left.b9 := by simpa only [h6] using hx'
  have h9 : x.left.b9=x.left.b2+x.left.b2*x.left.b4+x.left.b4*x.left.b5+x.left.b8 := by
    have he : x.left.b2+x.left.b2*x.left.b4+x.left.b4*x.left.b5+x.left.b8+x.left.b9=0 := by
      rw [← product_b8]
      change ((normalizedInput x.left.b1 x.left.b2 x.left.b2 x.left.b4 x.left.b5
        x.left.b4 x.left.b7 x.left.b8 x.left.b9) * _).left.b8=0
      rw [← hx'', h]
      rfl
    simpa only [ZMod.neg_eq_self_mod_two] using (eq_neg_of_add_eq_zero_right he)
  apply SemidirectProduct.ext
  · apply Core.ext <;> first | assumption | rfl
  · exact hr

end Tits.AmalgamRigidity.FullRee.PointedPairs
