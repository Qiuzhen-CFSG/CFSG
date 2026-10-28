module
public import Theory.GroupAction.RegularWreathFunctionModule
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# The literal paired natural linear-three action

The actor is SL₃(2) wr C₂ and its module is the product of two natural
binary three-spaces. The right coordinate shifts the factors before the
left coordinates act by matrix multiplication. Point stabilizers below
refer to this action, not to an abstract family of parabolics.

Source: Aschbacher--Smith 10.1.1(3), 10.2.4 and 10.2.11,
printed pp.741,747,753--754.
-/

@[expose] public noncomputable section
open scoped Matrix
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural

abbrev Bit := Multiplicative (ZMod 2)
abbrev Eight := Multiplicative (Fin 3 → ZMod 2)
abbrev Actor := RegularWreathProduct Matrix.PSL3Two.SL Bit
abbrev Space := Bit → Eight

/-- The original binary column action, written multiplicatively. -/
@[instance_reducible] def eightAction : MulDistribMulAction Matrix.PSL3Two.SL Eight where
  smul a x := Multiplicative.ofAdd (Matrix.mulVec a.val x.toAdd)
  one_smul x := by
    change Multiplicative.ofAdd ((1 : Matrix _ _ _) *ᵥ x.toAdd) = x
    simp
  mul_smul a b x := by
    change Multiplicative.ofAdd ((a.val * b.val) *ᵥ x.toAdd) = _
    exact congrArg Multiplicative.ofAdd (Matrix.mulVec_mulVec x.toAdd a.val b.val).symm
  smul_one a := by change Multiplicative.ofAdd (a.val *ᵥ 0) = 1; simp
  smul_mul a x y := by
    change Multiplicative.ofAdd (a.val *ᵥ (x.toAdd + y.toAdd)) = _
    rw [Matrix.mulVec_add]
    rfl

/-- The paired action, with Mathlib's exact regular-wreath convention. -/
def action : Actor →* MulAut Space := by
  letI := eightAction
  letI := RegularWreathProduct.functionModule Matrix.PSL3Two.SL Bit Eight
  exact MulDistribMulAction.toMulAut Actor Space

theorem action_apply (g : Actor) (v : Space) (i : Bit) :
    action g v i = Multiplicative.ofAdd
      (Matrix.mulVec (g.left i).val (v (g.right⁻¹ * i)).toAdd) := rfl

/-- The matrices and the factor permutation are both detected by the natural action. -/
theorem action_injective : Function.Injective action := by
  let _ := eightAction
  let _ : FaithfulSMul Matrix.PSL3Two.SL Eight := {
    eq_of_smul_eq_smul := by
      intro a b h
      apply Subtype.ext
      apply Matrix.ext_iff_mulVec.mpr
      intro x
      exact congrArg Multiplicative.toAdd (h (Multiplicative.ofAdd x)) }
  let _ := RegularWreathProduct.functionModule Matrix.PSL3Two.SL Bit Eight
  let _ := RegularWreathProduct.functionModule_faithful Matrix.PSL3Two.SL Bit Eight
  intro a b h
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Space)
  intro v
  exact MulEquiv.congr_fun h v

/-- The literal stabilizer of a vector in the paired natural module. -/
def pointStabilizer (v : Space) : Subgroup Actor :=
  (MulAction.stabilizer (MulAut Space) v).comap action

@[simp] theorem mem_pointStabilizer (g : Actor) (v : Space) :
    g ∈ pointStabilizer v ↔ action g v = v := Iff.rfl

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
