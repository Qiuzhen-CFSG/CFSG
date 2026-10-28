module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.FieldSynchronization

/-!
# Synchronized first-layer commutators

The field automorphism forced by the mixed V₁/V₂ comparison relabels the
linear root. Its reflected line and both Suzuki middle lines then have a
single common scalar in V₂. Cancellation gives (10.8) as a literal source
equality and both remaining (10.7) factorizations modulo the actual T₂.

The native Suzuki chart is the triangular correction of the printed chart.
Consequently (10.7)(ii) has coefficient b*y, and (iii) has middle coefficient
(b+a*theta(a))*y; the cubic coefficient is unchanged. These are derived
from the actual action, with theta=titsEnd and q=2 included. No mixed
commutator identity or compatibility of fields is assumed.
Source: Fong--Seitz II (1974), printed p.223, (10.7)--(10.8).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- Whole source roots with the synchronized common field parameters. -/
def synchronizedPositiveChart : (i : RootPresentationRecognition.PositiveTables.Root) →
    RootPresentationRecognition.PositiveTables.Parameter m i ≃ positiveRoot Q split i
  | .inl j => (Multiplicative.ofAdd.trans (synchronizedLinearChart Q split c).toEquiv).trans
      (positiveRootEquiv Q split (pinnedInput Q split c) (.inl j)).toEquiv
  | .inr j => positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr j)

def synchronizedPositivePoint (i : RootPresentationRecognition.PositiveTables.Root)
    (a : RootPresentationRecognition.PositiveTables.Parameter m i) : X ⧸ Q.D :=
  synchronizedPositiveChart Q split c i a

theorem synchronized_reflected_coordinate (a : CoefficientField m) :
    reflectedLinearCoordinate Q split (pinnedInput Q split c)
      (synchronizedPositiveChart Q split c (.inl 1) a) = a*pinnedLinearV2Label Q split c 1 := by
  change pinnedLinearV2Label Q split c (V1BasisLabel Q split (pinnedInput Q split c) a) = _
  rw [pinnedLinearV2Label_formula,AddEquiv.symm_apply_apply]

theorem synchronized_reflected_coordinates (a : CoefficientField m) :
    V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (V2ReflectedLinear Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inl 1) a))) =
      ![a*pinnedLinearV2Label Q split c 1,0,0,0] := by
  rw [V2Coordinates_reflectedLinear]
  change ![reflectedLinearCoordinate Q split (pinnedInput Q split c)
    (synchronizedPositiveChart Q split c (.inl 1) a),0,0,0] = _
  rw [synchronized_reflected_coordinate]

theorem synchronized_shifted_coordinates (a b : CoefficientField m) :
    V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (V2ShiftedSuzuki Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inr 3) (a,b)))) =
      ![0,a*pinnedLinearV2Label Q split c 1,0,0] := by
  have h := pinnedV2_shifted_parameter Q split c a b
  change V2Coordinates Q split (pinnedInput Q split c) _ =
    ![0,V2MiddleFieldLabel Q split c a,0,0] at h
  rw [V2MiddleFieldLabel_scalar] at h
  exact h

theorem synchronized_opposite_coordinates (a b : CoefficientField m) :
    V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (V2OppositeSuzuki Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inr 2) (a,b)))) =
      ![0,0,a*pinnedLinearV2Label Q split c 1,0] := by
  have h := pinnedV2_opposite_parameter Q split c a b
  change V2Coordinates Q split (pinnedInput Q split c) _ =
    ![0,0,V2MiddleFieldLabel Q split c a,0] at h
  rw [V2MiddleFieldLabel_scalar] at h
  exact h

theorem synchronized_reflected_from_label (a : CoefficientField m) :
    positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inl 1)
      ((reflectedLinearFieldLabel Q split (pinnedInput Q split c) (RingEquiv.refl _)).symm
        (a*pinnedLinearV2Label Q split c 1)) =
      synchronizedPositiveChart Q split c (.inl 1) a := by
  apply reflectedLinearCoordinate_injective Q split (pinnedInput Q split c)
  rw [synchronized_reflected_coordinate]
  exact (reflectedLinearFieldLabel Q split (pinnedInput Q split c) (RingEquiv.refl _)).apply_symm_apply _

theorem synchronized_middle_inverse (a y : CoefficientField m) :
    (V2MiddleFieldLabel Q split c).symm (a*V2MiddleFieldLabel Q split c y) = a*y := by
  apply (V2MiddleFieldLabel Q split c).injective
  rw [AddEquiv.apply_symm_apply,V2MiddleFieldLabel_scalar,V2MiddleFieldLabel_scalar,mul_assoc]

/-- The synchronized identity (10.8), in the actual source group. -/
theorem synchronized_ten_eight (a b y z : CoefficientField m) :
    (synchronizedPositivePoint Q split c (.inr 3) (y,z))⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ *
      synchronizedPositivePoint Q split c (.inr 3) (y,z) *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) =
      synchronizedPositivePoint Q split c (.inl 1) (a*y) := by
  have h := pinned_shiftedSuzuki_right_commutator Q split c (RingEquiv.refl _) a b y z
  rw [V2MiddleFieldLabel_scalar,←mul_assoc] at h
  exact h.trans (congrArg Subtype.val (synchronized_reflected_from_label Q split c (a*y)))

/-- (10.7)(ii) in the corrected native chart: its last coefficient is b*y. -/
theorem synchronized_ten_seven_ii (a b y z : CoefficientField m) :
    QuotientGroup.mk (V2RightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b))
      (inclusion (positiveRoot_le_remainder Q split (pinnedInput Q split c) (.inr 2) 1 (by decide))
        (synchronizedPositiveChart Q split c (.inr 2) (y,z)))) =
      V2ShiftedSuzuki Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inr 3) (titsEnd m a*y,0)) *
      V2ReflectedLinear Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inl 1) (b*y)) := by
  have h := V2_cross_commutator_factorization Q split c (RingEquiv.refl _) a b y z
  rw [synchronized_middle_inverse,V2MiddleFieldLabel_scalar,←mul_assoc,synchronized_reflected_from_label] at h
  exact h

/-- (10.7)(iii) on the same quotient, with the native Suzuki correction retained. -/
theorem synchronized_ten_seven_iii (a b y : CoefficientField m) :
    QuotientGroup.mk (V2RightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b))
      (inclusion (simpleLinear_le_suzukiRemainder Q split (pinnedInput Q split c))
        (synchronizedLinearChart Q split c (.ofAdd y)))) =
      V2OppositeSuzuki Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inr 2) (a*y,0)) *
      V2ShiftedSuzuki Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inr 3) ((b+a*titsEnd m a)*y,0)) *
      V2ReflectedLinear Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inl 1) ((a^2*titsEnd m a+a*b+titsEnd m b)*y)) := by
  let d := pinnedInput Q split c
  let v : (V2Section Q split d).numerator :=
    inclusion (simpleLinear_le_suzukiRemainder Q split d) (synchronizedLinearChart Q split c (.ofAdd y))
  have hv := synchronizedLinearChart_V2 Q split c y
  have h := V2RightCommutator_coordinates Q split d a b v
  dsimp only at h
  change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk v)) = _ at hv
  rw [hv] at h
  apply (V2Coordinates Q split d).injective
  change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk
    (V2RightCommutator Q split d (suzukiChart Q split d (a,b)) v))) =
      (V2Coordinates Q split d).toLinearEquiv
        ((Additive.ofMul (V2OppositeSuzuki Q split d
          (synchronizedPositiveChart Q split c (.inr 2) (a*y,0))) +
        Additive.ofMul (V2ShiftedSuzuki Q split d
          (synchronizedPositiveChart Q split c (.inr 3) ((b+a*titsEnd m a)*y,0)))) +
        Additive.ofMul (V2ReflectedLinear Q split d
          (synchronizedPositiveChart Q split c (.inl 1) ((a^2*titsEnd m a+a*b+titsEnd m b)*y))))
  rw [map_add,map_add]
  change _ = V2Coordinates Q split d (Additive.ofMul (V2OppositeSuzuki Q split d _)) +
    V2Coordinates Q split d (Additive.ofMul (V2ShiftedSuzuki Q split d _)) +
    V2Coordinates Q split d (Additive.ofMul (V2ReflectedLinear Q split d _))
  rw [h,synchronized_opposite_coordinates,synchronized_shifted_coordinates,synchronized_reflected_coordinates]
  ext i
  fin_cases i <;> simp <;> ring

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
