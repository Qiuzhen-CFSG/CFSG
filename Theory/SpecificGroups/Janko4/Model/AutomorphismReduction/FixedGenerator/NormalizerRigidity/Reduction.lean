module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.Residual
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant

/-!
# Unsquared membership reduced to the concrete central twist

An ambient normalizer of C acts on Q = O₂(C). The proved self-normalizer of
the local action supplies c ∈ C with that same action on Q. The corrected
matrix c⁻¹u fixes Q pointwise. The character calculation in `Residual` leaves
only X ↦ aX, Y ↦ Y; an explicit matrix-intertwiner obstruction removes this
case. The remaining matrix centralizes C and the proved commutant calculation
places it in the actual J₄ group. Multiplication by c gives membership of u.

Only the concrete intertwiner obstruction remains a premise here. Its producer
is `TwistedCertificate`, and the parent extension discharges it. This is an
intrinsic input toward Aschbacher–Smith 16.1.5(9), printed p.1172.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerRigidity
open NormalizerSquares NormalizerSquares.TwoCoreCentralizerData

/-- The precise matrix obstruction, independent of full group normalization. -/
@[expose] def NoTwistedUnit : Prop :=
  ∀ u : BinaryMatrixˣ,
    u * matrixUnitA = matrixUnitA * u →
    u * (localX : BinaryMatrixˣ) = matrixUnitA * (localX : BinaryMatrixˣ) * u →
    u * (localY : BinaryMatrixˣ) = (localY : BinaryMatrixˣ) * u → False

/-- Correcting on Q produces an ambient unit with pointwise trivial action on Q. -/
theorem exists_twoCore_correction (u : BinaryMatrixˣ)
    (hu : u ∈ Subgroup.normalizer (involutionCentralizer : Set BinaryMatrixˣ)) :
    ∃ (c : involutionCentralizer)
      (hv : (c : BinaryMatrixˣ)⁻¹ * u ∈
        Subgroup.normalizer (involutionCentralizer : Set BinaryMatrixˣ)),
      MulAut.characteristic involutionTwoCore
        (involutionCentralizer.normalizerMonoidHom ⟨(c : BinaryMatrixˣ)⁻¹ * u, hv⟩) = 1 := by
  let α := involutionCentralizer.normalizerMonoidHom ⟨u, hu⟩
  obtain ⟨c, hc⟩ := localTwoCoreActionSelfNormalizer localTwoCoreCentralizerControl
    (Subgroup.characteristic_mem_normalizer_conjNormal_range involutionTwoCore α)
  have hv : (c : BinaryMatrixˣ)⁻¹ * u ∈
      Subgroup.normalizer (involutionCentralizer : Set BinaryMatrixˣ) :=
    (Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).inv_mem (involutionCentralizer.le_normalizer c.property)) hu
  refine ⟨c, hv, ?_⟩
  have he : involutionCentralizer.normalizerMonoidHom
      ⟨(c : BinaryMatrixˣ)⁻¹ * u, hv⟩ = MulAut.conj c⁻¹ * α := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ((c : BinaryMatrixˣ)⁻¹ * u) * (x : BinaryMatrixˣ) *
        ((c : BinaryMatrixˣ)⁻¹ * u)⁻¹ =
      (c : BinaryMatrixˣ)⁻¹ * (u * (x : BinaryMatrixˣ) * u⁻¹) *
        ((c : BinaryMatrixˣ)⁻¹)⁻¹
    group
  rw [he, map_mul, Subgroup.characteristic_conj_eq_conjNormal]
  change MulAut.conjNormal c⁻¹ * MulAut.characteristic involutionTwoCore α = 1
  change MulAut.conjNormal c = MulAut.characteristic involutionTwoCore α at hc
  rw [← hc, map_inv, inv_mul_cancel]

/-- A matrix realization of a pointwise Q-fixer has trivial action on C,
provided the remaining concrete twist has no invertible intertwiner. -/
theorem localAction_eq_one_of_noTwistedUnit (hexcl : NoTwistedUnit)
    (v : BinaryMatrixˣ)
    (hv : v ∈ Subgroup.normalizer (involutionCentralizer : Set BinaryMatrixˣ))
    (hQ : MulAut.characteristic involutionTwoCore
      (involutionCentralizer.normalizerMonoidHom ⟨v, hv⟩) = 1) :
    involutionCentralizer.normalizerMonoidHom ⟨v, hv⟩ = 1 := by
  let β := involutionCentralizer.normalizerMonoidHom ⟨v, hv⟩
  have commute_of_fixed (x : involutionCentralizer) (hx : β x = x) :
      v * (x : BinaryMatrixˣ) = (x : BinaryMatrixˣ) * v := by
    have he := congrArg (fun z : involutionCentralizer => (z : BinaryMatrixˣ)) hx
    change v * (x : BinaryMatrixˣ) * v⁻¹ = (x : BinaryMatrixˣ) at he
    have hh := congrArg (fun z => z * v) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  rcases localX_cases β hQ with hx | hx
  · exact eq_one_of_fixes_localX β hQ hx
  · exfalso
    apply hexcl v
    · exact commute_of_fixed centralInvolution
        (fixes_twoCore β hQ _ centralInvolution_mem_twoCore)
    · have he := congrArg (fun z : involutionCentralizer => (z : BinaryMatrixˣ)) hx
      change v * (localX : BinaryMatrixˣ) * v⁻¹ =
        matrixUnitA * (localX : BinaryMatrixˣ) at he
      have hh := congrArg (fun z => z * v) he
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
    · exact commute_of_fixed localY (fixes_localY β hQ)

/-- Literal unsquared membership from the single explicit intertwiner obstruction. -/
theorem mem_of_noTwistedUnit (hexcl : NoTwistedUnit) (u : BinaryMatrixˣ)
    (hun : u ∈ Subgroup.normalizer (matrixGroup : Set BinaryMatrixˣ))
    (hua : u * matrixUnitA = matrixUnitA * u) : u ∈ matrixGroup := by
  obtain ⟨c, hv, hQ⟩ := exists_twoCore_correction u
    (normalizes_involutionCentralizer u hun hua)
  have he := localAction_eq_one_of_noTwistedUnit hexcl _ hv hQ
  have hcent : (c : BinaryMatrixˣ)⁻¹ * u ∈
      Subgroup.centralizer (involutionCentralizer : Set BinaryMatrixˣ) := by
    intro x hx
    have hf := congrArg (fun z : involutionCentralizer => (z : BinaryMatrixˣ))
      (DFunLike.congr_fun he ⟨x, hx⟩)
    change ((c : BinaryMatrixˣ)⁻¹ * u) * x *
      ((c : BinaryMatrixˣ)⁻¹ * u)⁻¹ = x at hf
    have hh := congrArg (fun z => z * ((c : BinaryMatrixˣ)⁻¹ * u)) hf
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  have hm := localMatrixCentralizer_of_commutant localMatrixCommutant hcent
  have he := matrixGroup.mul_mem (involutionCentralizer_le_matrixGroup c.property) hm
  simpa only [mul_inv_cancel_left] using he

end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity
