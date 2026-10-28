module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.SuzukiRigidity.UnsignedAction
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.SuzukiRigidity.OppositeScales.FourLines
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.SuzukiRigidity.OppositeScales.CentralBraid

/-!
# Inverse scales on opposite Suzuki blocks

Apply the automorphism to the alternating five-factor relation between the
opposite central elements at parameter one. Their images have parameters
`N(c true)` and `N(c false)`, where `N(t) = theta(t)^2*t`. The four-line
parameter test forces their product to be one. Multiplicativity and
injectivity of `N` then force `c false = (c true)⁻¹`.

`CentralBraid` proves the constant relation in the actual split F₄ group by
faithfulness of the binary Levi action, followed by coefficient-field
transport. Hence `suzuki_scales_inverse` requires only the supplied unsigned
action, with no extra relation, torus realization or automorphism coverage
premise.

Source: GLS3, Table 2.4 type V, 2.4.5(d), and the diagonal and field actions
in 2.5.1(b,c), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open SuzukiRigidity.OppositeScales
variable {m : ℕ}

/-- The actual central braid suffices to match the two Suzuki scales.
This conditional reduction uses only the supplied unsigned action. -/
theorem suzuki_scales_inverse_of_central_braid
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup) (C : SuzukiCoordinates d)
    (c : Bool → (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
    (hsu : UnsignedSuzukiAction d a C c σ)
    (hbraid : fivefold (suzukiWord m true 0 1) (suzukiWord m false 0 1) =
      fivefold (suzukiWord m false 0 1) (suzukiWord m true 0 1)) :
    c false = (c true)⁻¹ := by
  have hfixed : fivefold (C.element true 0 1) (C.element false 0 1) =
      fivefold (C.element false 0 1) (C.element true 0 1) := Subtype.ext hbraid
  have hcentral (positive : Bool) : a (C.element positive 0 1) =
      C.element positive 0 (suzukiSquareParameter (c positive : CoefficientField m)) := by
    simpa only [map_zero, mul_zero, map_one, mul_one] using hsu positive 0 1
  have ha := congrArg a hfixed
  simp only [fivefold, map_mul, hcentral] at ha
  have hne (positive : Bool) : suzukiSquareParameter (c positive : CoefficientField m) ≠ 0 :=
    suzukiSquareParameter_eq_zero.not.mpr (Units.ne_zero _)
  have hn := central_fivefold_parameters
    (suzukiSquareParameter (c true : CoefficientField m))
    (suzukiSquareParameter (c false : CoefficientField m)) (hne true) (hne false)
    (congrArg Subtype.val ha)
  have hi : Function.Injective (suzukiSquareParameter (m := m)) :=
    Finite.injective_iff_surjective.mpr suzukiSquareParameter_surjective
  have he : (c true : CoefficientField m) * (c false : CoefficientField m) = 1 := by
    apply hi
    rw [suzukiSquareParameter_mul, hn]
    simp [suzukiSquareParameter]
  exact eq_inv_of_mul_eq_one_right (Units.ext he)

/-- A pure Suzuki action with a common field map has inverse scales on the
two opposite blocks. The central braid is proved in the actual ambient group. -/
theorem suzuki_scales_inverse
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup) (C : SuzukiCoordinates d)
    (c : Bool → (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
    (hsu : UnsignedSuzukiAction d a C c σ) :
    c false = (c true)⁻¹ :=
  suzuki_scales_inverse_of_central_braid d a C c σ hsu (central_fivefold m)

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
end
