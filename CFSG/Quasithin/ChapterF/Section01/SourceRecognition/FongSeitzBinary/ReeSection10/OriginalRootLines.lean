module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiRootLine
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalCharts

/-!
# Original marked lifts of the two distinguished natural lines

The original endpoint two-core and its Frattini subgroup contain injective
lifts of the reflected linear root and shifted Suzuki Omega. Their natural
coordinates are exactly the first coordinate lines identified in (10.4)
and before (10.11). Every lift has its literal marked endpoint formula,
and specialization to the original marking gives the unchanged quotient
map Q.q. The lifts agree with the existing original positive-root charts,
so both ordered endpoint inclusion squares are retained. The general
marking also accepts the geometric amalgam.

Source: Fong--Seitz II (1974), printed pp.222 and 224. These line
identifications precede the common-field commutator comparison and do not
assert the complete Section 10 reconstruction.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

def originalReflectedLinear : positiveRoot Q split (.inl 1) →* pCore 2 (parabolic L S 1) :=
  (originalV2NumeratorEquiv Q e split c).symm.toMonoidHom.comp
    (inclusion (reflectedLinear_le_suzukiRemainder Q split c))

theorem originalReflectedLinear_injective : Function.Injective (originalReflectedLinear Q e split c) :=
  (originalV2NumeratorEquiv Q e split c).symm.injective.comp (inclusion_injective _)

theorem originalReflectedLinear_endpoint (a : positiveRoot Q split (.inl 1)) :
    endpointMap Q e 1 (originalReflectedLinear Q e split c a) = a :=
  congrArg Subtype.val ((originalV2NumeratorEquiv Q e split c).apply_symm_apply _)

theorem originalReflectedLinear_coordinates (a : positiveRoot Q split (.inl 1)) :
    originalV2Coordinates Q e split c
      (Additive.ofMul (QuotientGroup.mk (originalReflectedLinear Q e split c a))) =
        ![reflectedLinearCoordinate Q split c a,0,0,0] := by
  have he := congrArg (fun v : (V2Section Q split c).numerator =>
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v)))
    ((originalV2NumeratorEquiv Q e split c).apply_symm_apply
      (inclusion (reflectedLinear_le_suzukiRemainder Q split c) a))
  exact he.trans (V2Coordinates_reflectedLinear Q split c a)

def originalShiftedOmega : omegaOneAmbient (positiveRoot Q split (.inr 3)) →*
    frattini (pCore 2 (parabolic L S 1)) :=
  (originalPhiNumeratorEquiv Q e split c).symm.toMonoidHom.comp
    (inclusion (shiftedOmega_le_phi Q split c))

theorem originalShiftedOmega_injective : Function.Injective (originalShiftedOmega Q e split c) :=
  (originalPhiNumeratorEquiv Q e split c).symm.injective.comp (inclusion_injective _)

theorem originalShiftedOmega_endpoint (a : omegaOneAmbient (positiveRoot Q split (.inr 3))) :
    endpointMap Q e 1 (originalShiftedOmega Q e split c a).val.val = a :=
  congrArg Subtype.val ((originalPhiNumeratorEquiv Q e split c).apply_symm_apply _)

theorem originalShiftedOmega_coordinates (a : omegaOneAmbient (positiveRoot Q split (.inr 3))) :
    originalPhiCenterCoordinates Q e split c
      (Additive.ofMul (QuotientGroup.mk (originalShiftedOmega Q e split c a))) =
        ![shiftedOmegaCoordinate Q split c a,0,0,0] := by
  have he := congrArg (fun v : (phiCenterSection Q split c).numerator =>
    phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v)))
    ((originalPhiNumeratorEquiv Q e split c).apply_symm_apply
      (inclusion (shiftedOmega_le_phi Q split c) a))
  exact he.trans (phiCenterCoordinates_shiftedOmega Q split c a)

theorem originalReflectedLinear_positivePoint
    (h : HypothesisF11 L S) (σ : ReeF4.CoefficientField m ≃+* ReeF4.CoefficientField m)
    (a : ReeF4.CoefficientField m) :
    (originalReflectedLinear Q e split c (positiveChart Q split c σ (.inl 1) a) : G) =
      originalPositivePoint Q e h split c σ (.inl 1) a := by
  have he : (originalReflectedLinear Q e split c
      (positiveChart Q split c σ (.inl 1) a)).val =
      (⟨originalPositivePoint Q e h split c σ (.inl 1) a,
        (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q e h split c σ (.inl 1) a).property⟩ : parabolic L S 1) := by
    apply (Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective
    change endpointMap Q e 1 _ = endpointMap Q e 1 _
    rw [originalReflectedLinear_endpoint, originalPositivePoint_endpoint]
    rfl
  exact congrArg Subtype.val he

theorem originalShiftedOmega_positivePoint (h : HypothesisF11 L S) (a : ReeF4.CoefficientField m) :
    ((originalShiftedOmega Q e split c (shiftedOmegaPoint Q split c a)).val.val : G) =
      originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 3) (0,a) := by
  have he : (originalShiftedOmega Q e split c (shiftedOmegaPoint Q split c a)).val.val =
      (⟨originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 3) (0,a),
        (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 3) (0,a)).property⟩ :
            parabolic L S 1) := by
    apply (Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective
    change endpointMap Q e 1 _ = endpointMap Q e 1 _
    rw [originalShiftedOmega_endpoint, originalPositivePoint_endpoint]
    rfl
  exact congrArg Subtype.val he

theorem originalReflectedLinear_endpoints
    (h : HypothesisF11 L S) (σ : ReeF4.CoefficientField m ≃+* ReeF4.CoefficientField m)
    (a : ReeF4.CoefficientField m) (i : Fin 2) :
    ∃ hi : (originalReflectedLinear Q e split c (positiveChart Q split c σ (.inl 1) a) : G)
        ∈ parabolic L S i,
      endpointMap Q e i
        ⟨(originalReflectedLinear Q e split c (positiveChart Q split c σ (.inl 1) a) : G),hi⟩ =
        positivePoint Q split c σ (.inl 1) a := by
  rw [originalReflectedLinear_positivePoint Q e split c h σ a]
  exact ⟨_, originalPositivePoint_endpoint Q e h split c σ i (.inl 1) a⟩

theorem originalShiftedOmega_endpoints (h : HypothesisF11 L S)
    (a : ReeF4.CoefficientField m) (i : Fin 2) :
    ∃ hi : ((originalShiftedOmega Q e split c (shiftedOmegaPoint Q split c a)).val.val : G)
        ∈ parabolic L S i,
      endpointMap Q e i
        ⟨((originalShiftedOmega Q e split c (shiftedOmegaPoint Q split c a)).val.val : G),hi⟩ =
        positivePoint Q split c (RingEquiv.refl _) (.inr 3) (0,a) := by
  rw [originalShiftedOmega_positivePoint Q e split c h a]
  exact ⟨_, originalPositivePoint_endpoint Q e h split c (RingEquiv.refl _) i (.inr 3) (0,a)⟩

theorem originalReflectedLinear_fieldLabel
    (σ : ReeF4.CoefficientField m ≃+* ReeF4.CoefficientField m) (a : ReeF4.CoefficientField m) :
    originalV2Coordinates Q e split c (Additive.ofMul (QuotientGroup.mk
      (originalReflectedLinear Q e split c (positiveChart Q split c σ (.inl 1) a)))) =
        ![reflectedLinearFieldLabel Q split c σ a,0,0,0] :=
  originalReflectedLinear_coordinates Q e split c _

theorem originalShiftedOmega_fieldLabel (a : ReeF4.CoefficientField m) :
    originalPhiCenterCoordinates Q e split c (Additive.ofMul (QuotientGroup.mk
      (originalShiftedOmega Q e split c (shiftedOmegaPoint Q split c a)))) =
        ![shiftedOmegaFieldLabel Q split c a,0,0,0] :=
  originalShiftedOmega_coordinates Q e split c _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

theorem originalReflectedLinear_quotient (a : positiveRoot Q split (.inl 1)) :
    Q.q ⟨originalReflectedLinear Q (originalMarkedIso Q) split c a,
      parabolic_le_generated 1
        (originalReflectedLinear Q (originalMarkedIso Q) split c a).val.property⟩ = a :=
  (originalMarkedIso_right_apply Q _).symm.trans
    (originalReflectedLinear_endpoint Q (originalMarkedIso Q) split c a)

theorem originalShiftedOmega_quotient (a : omegaOneAmbient (positiveRoot Q split (.inr 3))) :
    Q.q ⟨(originalShiftedOmega Q (originalMarkedIso Q) split c a).val.val,
      parabolic_le_generated 1
        (originalShiftedOmega Q (originalMarkedIso Q) split c a).val.val.property⟩ = a :=
  (originalMarkedIso_right_apply Q _).symm.trans
    (originalShiftedOmega_endpoint Q (originalMarkedIso Q) split c a)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
