module

public import Theory.Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
public import Theory.Representation.SL3.AdjointCubicCentralizer.RootPlaneNormalForm

/-!
# The root-plane cubic bound on the original Frattini action

Graph compatibility makes the marked whole Frattini representation ordinary.
For a cubic generator whose projective action is outer and preserves a root
plane, the proved matrix normal form supplies the 256 fixed-point lower bound
on that same quotient and under the same inclusion. No diagonal group marker
or matrix conjugator remains as an input.

Source: Aschbacher--Smith B.4.14, printed p.98, and the nonblock endgame
for original 4.3.2, printed pp.618--619. The original component marking,
corrected graph descent, and literal root-plane preservation are supplied
by the source construction.
-/

public noncomputable section
open Matrix Representation Subgroup
open scoped MatrixGroups
open Matrix.PSL3.ExtensionBorel Matrix.PSL3.RootPlaneGeometry
namespace Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent

variable {N F : Type*} [Group N] [Finite N] [Field F] [Finite F] [CharP F 2]
  {B E : Subgroup N} [B.Normal] {hBE : B ≤ E}

/-- The original Frattini quotient has at least 256 fixed points under a
root-plane-preserving outer cubic, with no split-diagonal premise. -/
theorem FrattiniGraphData.fixed_card_ge_of_rootPlane
    (d : FrattiniGraphData (F := F) B E hBE) (hF : Nat.card F = 4)
    {X : Type*} [Group X] (j : X →* E) (x : X) (hx : zpowers x = ⊤)
    (hx3 : x ^ 3 = 1) (b : Bool)
    (hout : (pglEquivInnerDiagonal F (d.projection (j x))).val ∉
      MulAut.innerSubgroup PSL(3,F))
    (hroot : (rootPlane F b).map
      (pglEquivInnerDiagonal F (d.projection (j x))).val.toMonoidHom = rootPlane F b) :
    let : MulDistribMulAction X (Frattini B) :=
      MulDistribMulAction.compHom _ ((coreAction B).comp (E.subtype.comp j))
    256 ≤ Nat.card (FixedPoints.subgroup X (Frattini B)) := by
  let : MulDistribMulAction X (Frattini B) :=
    MulDistribMulAction.compHom _ ((coreAction B).comp (E.subtype.comp j))
  let e : Frattini B ≃ TraceZero F :=
    { toFun v := (d.coordinates v).toAdd
      invFun w := d.coordinates.symm (Multiplicative.ofAdd w)
      left_inv v := d.coordinates.symm_apply_apply v
      right_inv w := congrArg Multiplicative.toAdd
        (d.coordinates.apply_symm_apply (Multiplicative.ofAdd w)) }
  have hc : d.projection (j x) ^ 3 = 1 := by
    rw [←map_pow, ←map_pow, hx3, map_one, map_one]
  apply RootPlaneNormalForm.fixed_card_ge_of_rootPlane F hF
    (d.projection (j x)) b hc hout hroot x hx e
  intro v
  exact d.ordinary_action hF (j x) v

end Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
