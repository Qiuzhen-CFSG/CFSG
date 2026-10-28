module
public import Theory.Representation.BinaryAlternatingSixModels
public import Theory.Representation.TensorInvolutionDisplacement

/-!
# Excluding Steinberg quotients by small involution displacement

Both natural four-spaces are faithful. An involution therefore has rank
one or two on each, and the tensor displacement formula gives rank at
least six. This suffices to exclude a tensor quotient when the original
module has displacement at most two. Surjective equivariant maps can
only decrease displacement, so the conclusion retains the actual actor
and quotient map. The precise odd-involution rank is not required.

Source: Aschbacher--Smith, 13.8.33, printed p.967, the two Steinberg
exclusions after abelianness of U_L. The actual source-section consumer
is CaseOne.SteinbergSmallMovement.
-/

public section
open Representation Subgroup
open Representation.BinaryOffender.NaturalTensor
open Theory.SpecificGroups.SymmetricSix
namespace BinaryAlternatingSix

private theorem first_injective : Function.Injective firstNatural := by
  intro g h he
  apply polarRepresentation_injective
  apply Subtype.ext
  exact congrArg LinearMap.toMatrix' he

private theorem displacement_pos {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (A : Module.End (ZMod 2) W) (hA : A ≠ 1) :
    0 < operatorFixedCodim A := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hr : LinearMap.range (A - 1) = ⊥ := Submodule.finrank_eq_zero.mp hz
  exact hA (sub_eq_zero.mp (LinearMap.range_eq_bot.mp hr))

/-- Every involution moves at least six dimensions of the tensor.
This bound suffices for the source codimension-two exclusion, without
an unnecessary classification of the odd involution ranks. -/
theorem tensor_involution_displacement_ge_six (a : S6) (ha : orderOf a = 2) :
    6 ≤ operatorFixedCodim (tensorAction a) := by
  have hne : a ≠ 1 := by intro he; simp [he] at ha
  have h₁ : firstNatural a ≠ 1 := by
    intro he
    exact hne (first_injective (he.trans (map_one firstNatural).symm))
  have h₂ : secondNatural a ≠ 1 := by
    intro he
    have hz : diagramAut a = 1 := first_injective (he.trans (map_one firstNatural).symm)
    exact hne (diagramAut.injective (hz.trans (map_one diagramAut).symm))
  have hs (ρ : Representation (ZMod 2) S6 NaturalModule) : ρ a * ρ a = 1 := by
    have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
    rw [← map_mul, ← pow_two, ha2, map_one]
  have hpos₁ := displacement_pos (firstNatural a) h₁
  have hpos₂ := displacement_pos (secondNatural a) h₂
  have hbound₁ := TensorInvolutionDisplacement.twice_displacement_le (firstNatural a) (hs firstNatural)
  have hbound₂ := TensorInvolutionDisplacement.twice_displacement_le (secondNatural a) (hs secondNatural)
  rw [naturalModule_finrank] at hbound₁ hbound₂
  have ht := TensorInvolutionDisplacement.tensor_displacement_formula
    (firstNatural a) (secondNatural a) (hs firstNatural) (hs secondNatural)
  change operatorFixedCodim (tensorAction a) +
    2 * operatorFixedCodim (firstNatural a) * operatorFixedCodim (secondNatural a) =
    Module.finrank (ZMod 2) NaturalModule * operatorFixedCodim (firstNatural a) +
    Module.finrank (ZMod 2) NaturalModule * operatorFixedCodim (secondNatural a) at ht
  rw [naturalModule_finrank] at ht
  have hr : operatorFixedCodim (firstNatural a) = 1 ∨ operatorFixedCodim (firstNatural a) = 2 := by omega
  have hs : operatorFixedCodim (secondNatural a) = 1 ∨ operatorFixedCodim (secondNatural a) = 2 := by omega
  rcases hr with hr | hr <;> rcases hs with hs | hs <;> rw [hr,hs] at ht <;> omega

/-- A module with an involution moving at most two dimensions cannot
surject equivariantly onto the Steinberg tensor. -/
theorem no_tensor_quotient_of_small_involution
    {B X : Type*} [Group B] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) B X) (e : B ≃* S6) (b : B)
    (hb : orderOf (e b) = 2) (hsmall : operatorFixedCodim (ρ b) ≤ 2)
    (q : ρ.IntertwiningMap (tensorAction.comp e.toMonoidHom)) : ¬ Function.Surjective q := by
  intro hq
  have hle := operatorFixedCodim_le_of_surjective (ρ b) (tensorAction (e b)) q.toLinearMap hq
    (IntertwiningMap.isIntertwining _ _ q b)
  have hlo := tensor_involution_displacement_ge_six (e b) hb
  omega

end BinaryAlternatingSix
