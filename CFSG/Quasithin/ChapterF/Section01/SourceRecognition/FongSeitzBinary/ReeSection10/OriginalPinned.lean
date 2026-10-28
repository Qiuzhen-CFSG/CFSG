module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PinnedNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalRootLines

/-!
# Original representatives of the pinned opposite natural lines

Transport the simple linear root and Ω₁(U₂^s₁) through the original endpoint
isomorphism into O₂(P₂) and its Frattini subgroup. Their pinned natural
coordinates are the fourth axes with the same labels as the first axes.
The representatives agree with the existing positive-root points, so both
ordered endpoint inclusion squares and the literal original quotient Q.q
are preserved. A general marked isomorphism also accepts the geometric
source amalgam. Every statement includes the binary parameter.

Source: Fong--Seitz II (1974), (10.4) and the basis before (10.11),
printed pp.222 and 224. The remaining middle-line and coefficient
synchronization is not asserted by these endpoint transports.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
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

def originalSimpleLinear : simpleRoot Q split 0 →* pCore 2 (parabolic L S 1) :=
  (originalV2NumeratorEquiv Q e split c).symm.toMonoidHom.comp
    (inclusion (simpleLinear_le_suzukiRemainder Q split c))

theorem originalSimpleLinear_endpoint (a : simpleRoot Q split 0) :
    endpointMap Q e 1 (originalSimpleLinear Q e split c a) = a :=
  congrArg Subtype.val ((originalV2NumeratorEquiv Q e split c).apply_symm_apply _)

theorem originalSimpleLinear_coordinates (a : simpleRoot Q split 0) :
    originalV2Coordinates Q e split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk
        (originalSimpleLinear Q e split (pinnedInput Q split c) a))) =
      ![0,0,0,reflectedLinearCoordinate Q split (pinnedInput Q split c)
        (positiveRootEquiv Q split (pinnedInput Q split c) (.inl 1) a)] := by
  have he := congrArg (fun v : (V2Section Q split (pinnedInput Q split c)).numerator =>
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v)))
    ((originalV2NumeratorEquiv Q e split (pinnedInput Q split c)).apply_symm_apply
      (inclusion (simpleLinear_le_suzukiRemainder Q split (pinnedInput Q split c)) a))
  exact he.trans (pinnedV2_simpleLinear Q split c a)

theorem originalSimpleLinear_fieldLabel
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    originalV2Coordinates Q e split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk
        (originalSimpleLinear Q e split (pinnedInput Q split c)
          (linearChart Q split (pinnedInput Q split c) σ (.ofAdd a))))) =
      ![0,0,0,reflectedLinearFieldLabel Q split (pinnedInput Q split c) σ a] :=
  originalSimpleLinear_coordinates Q e split c _

def originalOppositeOmega (b : CoefficientField m) :
    frattini (pCore 2 (parabolic L S 1)) :=
  (originalPhiNumeratorEquiv Q e split c).symm (phiOppositeOmega Q split c b)

theorem originalOppositeOmega_endpoint (b : CoefficientField m) :
    endpointMap Q e 1 (originalOppositeOmega Q e split c b).val.val =
      positivePoint Q split c (RingEquiv.refl _) (.inr 2) (0,b) :=
  (congrArg Subtype.val ((originalPhiNumeratorEquiv Q e split c).apply_symm_apply _)).trans
    (phiOppositeOmega_point Q split c b)

theorem originalOppositeOmega_coordinates (b : CoefficientField m) :
    originalPhiCenterCoordinates Q e split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk
        (originalOppositeOmega Q e split (pinnedInput Q split c) b))) =
      ![0,0,0,shiftedOmegaFieldLabel Q split (pinnedInput Q split c) b] := by
  have he := congrArg (fun v : (phiCenterSection Q split (pinnedInput Q split c)).numerator =>
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v)))
    ((originalPhiNumeratorEquiv Q e split (pinnedInput Q split c)).apply_symm_apply
      (phiOppositeOmega Q split (pinnedInput Q split c) b))
  exact he.trans (pinnedPhiCenter_oppositeOmega Q split c b)

theorem originalSimpleLinear_positivePoint
    (h : HypothesisF11 L S) (σ : CoefficientField m ≃+* CoefficientField m)
    (a : CoefficientField m) :
    (originalSimpleLinear Q e split c (linearChart Q split c σ (.ofAdd a)) : G) =
      originalPositivePoint Q e h split c σ (.inl 0) a := by
  have he : (originalSimpleLinear Q e split c (linearChart Q split c σ (.ofAdd a))).val =
      (⟨originalPositivePoint Q e h split c σ (.inl 0) a,
        (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q e h split c σ (.inl 0) a).property⟩ : parabolic L S 1) := by
    apply (Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective
    change endpointMap Q e 1 _ = endpointMap Q e 1 _
    rw [originalSimpleLinear_endpoint,originalPositivePoint_endpoint]
    change (linearChart Q split c σ (.ofAdd a) : X ⧸ Q.D) =
      (1 : X ⧸ Q.D)⁻¹ * linearChart Q split c σ (.ofAdd a) * 1
    simp
  exact congrArg Subtype.val he

theorem originalOppositeOmega_positivePoint (h : HypothesisF11 L S) (b : CoefficientField m) :
    ((originalOppositeOmega Q e split c b).val.val : G) =
      originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 2) (0,b) := by
  have he : (originalOppositeOmega Q e split c b).val.val =
      (⟨originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 2) (0,b),
        (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 2) (0,b)).property⟩ :
          parabolic L S 1) := by
    apply (Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective
    change endpointMap Q e 1 _ = endpointMap Q e 1 _
    rw [originalOppositeOmega_endpoint,originalPositivePoint_endpoint]
  exact congrArg Subtype.val he

theorem originalSimpleLinear_endpoints (h : HypothesisF11 L S)
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) (i : Fin 2) :
    ∃ hi : (originalSimpleLinear Q e split c (linearChart Q split c σ (.ofAdd a)) : G)
        ∈ parabolic L S i,
      endpointMap Q e i
        ⟨(originalSimpleLinear Q e split c (linearChart Q split c σ (.ofAdd a)) : G),hi⟩ =
        positivePoint Q split c σ (.inl 0) a := by
  rw [originalSimpleLinear_positivePoint Q e split c h σ a]
  exact ⟨_,originalPositivePoint_endpoint Q e h split c σ i (.inl 0) a⟩

theorem originalOppositeOmega_endpoints (h : HypothesisF11 L S)
    (b : CoefficientField m) (i : Fin 2) :
    ∃ hi : ((originalOppositeOmega Q e split c b).val.val : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨((originalOppositeOmega Q e split c b).val.val : G),hi⟩ =
        positivePoint Q split c (RingEquiv.refl _) (.inr 2) (0,b) := by
  rw [originalOppositeOmega_positivePoint Q e split c h b]
  exact ⟨_,originalPositivePoint_endpoint Q e h split c (RingEquiv.refl _) i (.inr 2) (0,b)⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

theorem originalSimpleLinear_quotient (a : simpleRoot Q split 0) :
    Q.q ⟨originalSimpleLinear Q (originalMarkedIso Q) split c a,
      parabolic_le_generated 1
        (originalSimpleLinear Q (originalMarkedIso Q) split c a).val.property⟩ = a :=
  (originalMarkedIso_right_apply Q _).symm.trans
    (originalSimpleLinear_endpoint Q (originalMarkedIso Q) split c a)

theorem originalOppositeOmega_quotient (b : CoefficientField m) :
    Q.q ⟨(originalOppositeOmega Q (originalMarkedIso Q) split c b).val.val,
      parabolic_le_generated 1
        (originalOppositeOmega Q (originalMarkedIso Q) split c b).val.val.property⟩ =
      positivePoint Q split c (RingEquiv.refl _) (.inr 2) (0,b) :=
  (originalMarkedIso_right_apply Q _).symm.trans
    (originalOppositeOmega_endpoint Q (originalMarkedIso Q) split c b)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
