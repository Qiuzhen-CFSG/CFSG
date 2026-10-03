module
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenExceptionalCoordinates
/-!
# Multiplication in the exceptional Ree two subgroup

The nine binary coordinates have a class-two multiplication law. The even
cyclic-four action is checked on root generators, then extended using the
verified normal form. This avoids repeated expansion of the ambient action.

Source: Shinoda (1975), (2.3), pp. 81–82, via the verified Ree two model.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallEvenExceptional
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
def evenAction (a : ZMod 2) (y : Core) : Core :=
  ⟨y.b0,y.b1,y.b2,y.b3,y.b4,y.b5,y.b6,y.b7+a*y.b5,
    y.b8+a*(y.b5+y.b6),y.b9+a*y.b5⟩
def act (a : ZMod 2) : MulAut Core :=
  Core.complementAction (SemidirectProduct.inr (Multiplicative.ofAdd (2*a.val : ZMod 4)))
theorem root_act : ∀ (a : ZMod 2) (i : CoreRoot) (t : ZMod 2), 2 ≤ i.val →
    (act a (Core.root i)) ^ t.val = evenAction a (Core.root i ^ t.val) := by decide +kernel
theorem evenAction_test (a : ZMod 2) (v : Fin 8 → ZMod 2) :
    act a ⟨0,0,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7⟩ =
    evenAction a ⟨0,0,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7⟩ := by
  have hn := congrArg (act a) (Core.normal_form ⟨0,0,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7⟩)
  simp only [map_mul, map_pow, ZMod.val_zero, pow_zero, one_mul] at hn
  rw [← hn]
  rw [root_act a 2 _ (by decide), root_act a 3 _ (by decide),
    root_act a 4 _ (by decide), root_act a 5 _ (by decide),
    root_act a 6 _ (by decide), root_act a 7 _ (by decide),
    root_act a 8 _ (by decide), root_act a 9 _ (by decide)]
  simp only [Core.root_pow]
  have hm (x y : Core) : x*y = Core.mul x y := rfl
  apply Core.ext <;> simp [hm, Core.mul, Core.ofCoords, evenAction] <;> ring
def mulV (v w : V) : V :=
  ![v 0+w 0,v 1+w 1,v 2+w 2,v 3+w 3,v 4+w 4,v 5+w 5,
    v 6+w 6+v 2*w 1+v 0*w 4,
    v 7+w 7+v 3*w 1+v 2*w 2+v 0*(w 4+w 5),
    v 8+w 8+v 1*w 1+v 5*w 2+v 4*w 3+v 0*w 4]
theorem element_mul (v w : V) : element v * element w = element (mulV v w) := by
  apply SemidirectProduct.ext
  · change Core.mul _ (act (v 0)
      ⟨0,0,w 1,w 2,w 3,w 4,w 5,w 6,w 7,w 8⟩) = _
    have ha := evenAction_test (v 0) ![w 1,w 2,w 3,w 4,w 5,w 6,w 7,w 8]
    change act (v 0) ⟨0,0,w 1,w 2,w 3,w 4,w 5,w 6,w 7,w 8⟩ = _ at ha
    rw [ha]
    apply Core.ext <;> simp [Core.mul,evenAction,element,mulV] <;> ring
  · change Multiplicative.ofAdd ((2*(v 0).val : ZMod 4) + (2*(w 0).val : ZMod 4)) =
      Multiplicative.ofAdd (2*(v 0+w 0).val : ZMod 4)
    exact (by decide +kernel : ∀ a b : ZMod 2,
      Multiplicative.ofAdd ((2*a.val : ZMod 4)+(2*b.val : ZMod 4)) =
      Multiplicative.ofAdd (2*(a+b).val : ZMod 4)) _ _
end ReeTwo.SylowModel.SmallEvenExceptional
