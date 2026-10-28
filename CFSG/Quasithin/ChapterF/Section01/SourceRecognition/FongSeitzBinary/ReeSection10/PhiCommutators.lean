module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiMiddleLines

/-!
# Right commutators in the second Suzuki natural section

The source uses v⁻¹u⁻¹vu. In the literal Frattini numerator this is
v⁻¹ multiplied by conjugation of v by u⁻¹. Inverting the corrected Suzuki
chart changes b to b+a·θ(a), where θ=titsEnd. Expanding the already proved
natural action gives every coordinate of this right commutator; its cubic
coefficient is unchanged by inversion.

The four-root natural basis then realizes the resulting vector as a product
of actual source roots modulo the exact center. The perpendicular-linear
commutator is also proved in the source group itself in the right convention.
Additive field labels remain explicit, pending comparison with the other
Section 10 sections. All formulas include q = 2.

Source: Fong--Seitz II (1974), (10.11), p.224, and the chart convention
before (10.32), p.230. The triangular native-chart correction is the one
used in PositiveCharts; it is retained in the coefficient table here.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups ReeF4
open scoped IsMulCommutative commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- Inverse in the corrected native Suzuki chart. -/
theorem suzukiChart_inverse (a b : CoefficientField m) :
    (suzukiChart Q split c (a,b))⁻¹ = suzukiChart Q split c (a,b+a*titsEnd m a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [suzukiChart_mul]
  have h : b+(b+a*titsEnd m a)+titsEnd m a*a = 0 := by
    calc
      b+(b+a*titsEnd m a)+titsEnd m a*a =
        (b+b)+(a*titsEnd m a+a*titsEnd m a) := by ring
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
  rw [h,CharTwo.add_self_eq_zero,suzukiChart_zero]

/-- The actual right commutator v⁻¹u⁻¹vu inside the Frattini numerator.
The product uses the source inverse actor; it is not a Weyl-class action. -/
def phiRightCommutator (u : simpleRoot Q split 1)
    (v : (phiCenterSection Q split c).numerator) : (phiCenterSection Q split c).numerator :=
  v⁻¹ * (phiCenterSection Q split c).numeratorAction (inclusion le_sup_left u⁻¹) v

theorem phiRightCommutator_val (u : simpleRoot Q split 1)
    (v : (phiCenterSection Q split c).numerator) :
    (phiRightCommutator Q split c u v : X ⧸ Q.D) =
      (v : X ⧸ Q.D)⁻¹ * (u : X ⧸ Q.D)⁻¹ * v * u := by
  change (v : X ⧸ Q.D)⁻¹ * ((u : X ⧸ Q.D)⁻¹ * v * ((u : X ⧸ Q.D)⁻¹)⁻¹) = _
  group

/-- The exact mixed commutator also has the paper's right-commutator
convention, with the same unsynchronized coefficient. -/
theorem pinned_perpendicularLinear_right_commutator
    (σ : CoefficientField m ≃+* CoefficientField m) (a b y : CoefficientField m) :
    (positivePoint Q split (pinnedInput Q split c) σ (.inl 3) y)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ *
      positivePoint Q split (pinnedInput Q split c) σ (.inl 3) y *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) =
      positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3)
        (0,(shiftedOmegaFieldLabel Q split (pinnedInput Q split c)).symm
          (a * phiPerpendicularFieldLabel Q split c σ y)) := by
  let d := pinnedInput Q split c
  let u := suzukiChart Q split d (a,b)
  let v : (phiCenterSection Q split d).numerator :=
    inclusion (perpendicularLinear_le_phi Q split d) (positiveChart Q split d σ (.inl 3) y)
  let : IsElementaryAbelian 2 (phiCenterSection Q split d).numerator := phiRemainder_elementary Q split d
  have h := congrArg (fun z : (phiCenterSection Q split d).numerator => (z : X ⧸ Q.D))
    (mul_comm v⁻¹ ((phiCenterSection Q split d).numeratorAction (inclusion le_sup_left u⁻¹) v))
  have he : (v : X ⧸ Q.D)⁻¹ * (u : X ⧸ Q.D)⁻¹ * v * u =
      ⁅((u : X ⧸ Q.D)⁻¹),(v : X ⧸ Q.D)⁆ := by
    change (v : X ⧸ Q.D)⁻¹ * ((u : X ⧸ Q.D)⁻¹ * v * ((u : X ⧸ Q.D)⁻¹)⁻¹) =
      ((u : X ⧸ Q.D)⁻¹ * v * ((u : X ⧸ Q.D)⁻¹)⁻¹) * (v : X ⧸ Q.D)⁻¹ at h
    simpa only [commutatorElement_def,inv_inv,mul_assoc] using h
  apply he.trans
  have hk := pinned_perpendicularLinear_commutator Q split c σ a (b+a*titsEnd m a) y
  have hu : (u : X ⧸ Q.D)⁻¹ = (suzukiChart Q split d (a,b+a*titsEnd m a) : X ⧸ Q.D) :=
    congrArg Subtype.val (suzukiChart_inverse Q split d a b)
  change ⁅((u : X ⧸ Q.D)⁻¹), (v : X ⧸ Q.D)⁆ = _
  rw [hu]
  exact hk

/-- Right commutator coordinates on the literal second Suzuki layer, in the
corrected root chart. The cubic coefficient is unchanged on inversion. -/
theorem phiRightCommutator_coordinates (a b : CoefficientField m)
    (v : (phiCenterSection Q split c).numerator) :
    phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
      (phiRightCommutator Q split c (suzukiChart Q split c (a,b)) v))) =
      let x := phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v))
      ![a*x 1+b*x 2+(a^2*titsEnd m a+a*b+titsEnd m b)*x 3,
        titsEnd m a*x 2+(b+a*titsEnd m a)*x 3,a*x 3,0] := by
  let x := phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v))
  let r := (phiCenterSection Q split c).numeratorAction
    (inclusion le_sup_left (suzukiChart Q split c (a,b))⁻¹) v
  have hr : r = (phiCenterSection Q split c).numeratorAction
      (inclusion le_sup_left (suzukiChart Q split c (a,b+a*titsEnd m a))) v := by
    dsimp only [r]
    rw [suzukiChart_inverse]
  have hq : (QuotientGroup.mk (phiRightCommutator Q split c (suzukiChart Q split c (a,b)) v) :
      (phiCenterSection Q split c).Carrier) =
      (QuotientGroup.mk v)⁻¹ * QuotientGroup.mk r := by
    exact (QuotientGroup.mk' (phiCenterSection Q split c).denominator).map_mul v⁻¹ r |>.trans
      (by rw [map_inv]; rfl)
  have h := congrArg (fun w : (phiCenterSection Q split c).Carrier =>
    phiCenterCoordinates Q split c (Additive.ofMul w)) hq
  change _ = (phiCenterCoordinates Q split c).toLinearEquiv
    (-Additive.ofMul (QuotientGroup.mk v) + Additive.ofMul (QuotientGroup.mk r)) at h
  rw [map_add,map_neg] at h
  apply h.trans
  have he := congrArg (fun w : (phiCenterSection Q split c).numerator =>
    phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk w))) hr
  have he := he.trans (phiCenterCoordinates_suzukiChart Q split c a (b+a*titsEnd m a) v)
  change -x + phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk r)) = _
  rw [he]
  change -x + ![x 0+a*x 1+(b+a*titsEnd m a+a*titsEnd m a)*x 2+
      (a^2*titsEnd m a+a*(b+a*titsEnd m a)+titsEnd m (b+a*titsEnd m a))*x 3,
      x 1+titsEnd m a*x 2+(b+a*titsEnd m a)*x 3,x 2+a*x 3,x 3] = _
  simp only [map_add,map_mul,titsEnd_twice]
  ext i
  fin_cases i
  · dsimp
    linear_combination (norm := ring_nf)
      (a*x 2+a^2*x 3) * CharTwo.add_self_eq_zero (titsEnd m a)
    dsimp only [x]
    ring
  · dsimp; ring
  · dsimp; ring
  · dsimp; ring

/-- A four-root product for every right commutator in the second natural
section. Each coordinate is realized by the literal roots in the p.224 basis. -/
theorem phiRightCommutator_naturalPoint
    (σ : CoefficientField m ≃+* CoefficientField m) (a b : CoefficientField m)
    (v : (phiCenterSection Q split (pinnedInput Q split c)).numerator) :
    QuotientGroup.mk (phiRightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b)) v) =
      let x := phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v))
      phiNaturalPoint Q split c σ
        ![a*x 1+b*x 2+(a^2*titsEnd m a+a*b+titsEnd m b)*x 3,
          titsEnd m a*x 2+(b+a*titsEnd m a)*x 3,a*x 3,0] := by
  apply (phiCenterCoordinates Q split (pinnedInput Q split c)).injective
  exact (phiRightCommutator_coordinates Q split (pinnedInput Q split c) a b v).trans
    (phiNaturalPoint_coordinates Q split c σ _).symm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
