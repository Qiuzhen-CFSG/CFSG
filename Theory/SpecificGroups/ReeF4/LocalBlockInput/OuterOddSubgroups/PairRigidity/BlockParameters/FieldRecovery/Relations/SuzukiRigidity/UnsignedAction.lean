module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.SuzukiRigidity.TorusGeometry

/-!
# Pure Suzuki curves with the common linear field map

The end-node torus word intertwines the induced Suzuki parameter maps with
the field map already prescribed on the linear blocks. Evaluating its action
at parameter one gives semilinearity of the first coordinate and central
character homogeneity of the displacement. The square law then determines
the central action, and the nonadditivity of the Suzuki norm for `m ≥ 1`
forces the displacement to vanish.

This establishes both signs separately. The inverse relation between their
two nonzero scales remains an opposite-block calculation; it is not part of
`UnsignedSuzukiAction` or a consequence asserted here.

Sources: GLS3, Table 2.4 type V, 2.4.5(d), and 2.5.1(b,c), in
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open SuzukiRigidity
variable {m : ℕ}

/-- Independent pure actions on the two Suzuki signs. Inverse compatibility of
`c true` and `c false` is deliberately not included in this intermediate predicate. -/
def UnsignedSuzukiAction (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (C : SuzukiCoordinates d) (c : Bool → (CoefficientField m)ˣ)
    (σ : CoefficientField m ≃+* CoefficientField m) : Prop :=
  ∀ positive t u, a (C.element positive t u) =
    C.element positive ((c positive : CoefficientField m) * σ t)
      (suzukiSquareParameter (c positive : CoefficientField m) * σ u)

private theorem signedScale_twice (u : (CoefficientField m)ˣ) (positive : Bool) :
    signedScale (signedScale u positive) positive = u := by
  cases positive <;> simp [signedScale]

/-- The end-node torus intertwines the first and central coordinates with
exactly the field map already obtained on the linear blocks. -/
theorem suzuki_parameters_homogeneous (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
    (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
    (hlin : SignedLinearAction d a b σ) (positive : Bool) (v : CoefficientField m) :
    suzukiFirstParameter d a hb C positive v =
        suzukiFirstParameter d a hb C positive 1 * σ v ∧
      suzukiShear d a hb C positive v =
        suzukiSquareParameter (σ v) * suzukiShear d a hb C positive 1 := by
  by_cases hv : v = 0
  · subst v
    simp [suzukiFirstParameter_zero, suzukiShear_zero, suzukiSquareParameter]
  let z : (CoefficientField m)ˣ := signedScale (Units.mk0 v hv) positive
  have hz : (signedScale z positive : CoefficientField m) = v :=
    congrArg Units.val (signedScale_twice (Units.mk0 v hv) positive)
  have hf : (signedScale (Units.map σ.toMonoidHom z) positive : CoefficientField m) = σ v := by
    rw [← hz]
    cases positive <;> simp [signedScale]
  have h := congrArg a (linearWeyl_ratio_suzuki d C z⁻¹ 1 positive 1 0)
  simp only [inv_one, mul_one, inv_inv, mul_zero, hz] at h
  simp only [map_mul, map_inv, linearWeyl_action d a b σ hlin, map_one,
    mul_one, suzuki_action_pure d a hb C positive] at h
  rw [linearWeyl_ratio_suzuki] at h
  have hr : ((b * (Units.map σ.toMonoidHom z)⁻¹) * b⁻¹)⁻¹ = Units.map σ.toMonoidHom z := by
    simp [mul_comm, mul_left_comm]
  rw [hr, hf, ← suzukiSquareParameter_signedScale, hf] at h
  have he := C.element_injective positive h
  exact ⟨he.1.symm.trans (mul_comm _ _), he.2.symm⟩

/-- Signed linear semilinearity forces each Suzuki curve to be pure and to
use the same field map. At this stage the two nonzero scales are independent. -/
theorem exists_unsigned_suzuki_action (hm : 1 ≤ m)
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
    (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
    (hlin : SignedLinearAction d a b σ) :
    ∃ c : Bool → (CoefficientField m)ˣ, UnsignedSuzukiAction d a C c σ := by
  have hne (positive : Bool) : suzukiFirstParameter d a hb C positive 1 ≠ 0 := by
    intro h
    exact one_ne_zero (suzukiFirstParameter_injective d a hb C positive
      (h.trans (suzukiFirstParameter_zero d a hb C positive).symm))
  let c (positive : Bool) : (CoefficientField m)ˣ :=
    Units.mk0 (suzukiFirstParameter d a hb C positive 1) (hne positive)
  have hfirst (positive : Bool) (t : CoefficientField m) :
      suzukiFirstParameter d a hb C positive t = (c positive : CoefficientField m) * σ t :=
    (suzuki_parameters_homogeneous d a hb C b σ hlin positive t).1
  have hzero (positive : Bool) (t : CoefficientField m) :
      suzukiShear d a hb C positive t = 0 :=
    suzukiShear_eq_zero_of_homogeneous hm d a hb C positive (c positive) σ
      (hfirst positive)
      (fun v => (suzuki_parameters_homogeneous d a hb C b σ hlin positive v).2) t
  refine ⟨c, fun positive t u => ?_⟩
  rw [suzuki_action d a hb C, hfirst, hzero, zero_add,
    suzukiCentralParameter_of_first d a hb C positive (c positive) σ (hfirst positive)]
end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
end
