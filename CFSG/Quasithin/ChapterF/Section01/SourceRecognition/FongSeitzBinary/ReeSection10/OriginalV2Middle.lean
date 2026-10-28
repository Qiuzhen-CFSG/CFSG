module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.V2Commutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalPinned

/-!
# Original middle roots and basis of the first Suzuki quotient

The two Suzuki middle roots are transported into the original second
endpoint two-core and its literal quotient by T₂. Their coordinates share
the additive field label constructed on the marked source quotient.
The resulting four-root product is bijective onto that original quotient.
Both ordered endpoint inclusions and the original Q.q formula are proved
for the same positive-root representatives. The exact mixed commutator is
also transported back to the original Sylow through its injective marking.

The marking is arbitrary, so the same statements apply to the geometric
quotient, and all parameters m ≥ 0 are retained. Field synchronization,
the linear characteristic section and final presentation construction are
not inferred from these transports.

Source: Fong--Seitz II (1974), (10.4)--(10.8), pp.222--223.
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

def originalV2Shifted (a b : CoefficientField m) : pCore 2 (parabolic L S 1) :=
  (originalV2NumeratorEquiv Q e split c).symm
    (inclusion (positiveRoot_le_remainder Q split c (.inr 3) 1 (by decide))
      (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (a,b)))

theorem originalV2Shifted_endpoint (a b : CoefficientField m) :
    endpointMap Q e 1 (originalV2Shifted Q e split c a b) =
      positivePoint Q split c (RingEquiv.refl _) (.inr 3) (a,b) :=
  congrArg Subtype.val ((originalV2NumeratorEquiv Q e split c).apply_symm_apply _)

theorem originalV2Shifted_coordinates (a b : CoefficientField m) :
    originalV2Coordinates Q e split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk
        (originalV2Shifted Q e split (pinnedInput Q split c) a b))) = ![0,V2MiddleFieldLabel Q split c a,0,0] := by
  have he := congrArg (fun v : (V2Section Q split (pinnedInput Q split c)).numerator =>
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v)))
    ((originalV2NumeratorEquiv Q e split (pinnedInput Q split c)).apply_symm_apply
      (inclusion (positiveRoot_le_remainder Q split (pinnedInput Q split c) (.inr 3) 1 (by decide))
        (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (a,b))))
  exact he.trans (pinnedV2_shifted_parameter Q split c a b)

theorem originalV2Shifted_positivePoint (h : HypothesisF11 L S) (a b : CoefficientField m) :
    (originalV2Shifted Q e split c a b : G) =
      originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 3) (a,b) := by
  have he : (originalV2Shifted Q e split c a b).val =
      (⟨originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 3) (a,b),
        (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 3) (a,b)).property⟩ :
        parabolic L S 1) := by
    apply (Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective
    change endpointMap Q e 1 _ = endpointMap Q e 1 _
    rw [originalV2Shifted_endpoint,originalPositivePoint_endpoint]
  exact congrArg Subtype.val he

theorem originalV2Shifted_endpoints (h : HypothesisF11 L S)
    (a b : CoefficientField m) (i : Fin 2) :
    ∃ hi : (originalV2Shifted Q e split c a b : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨(originalV2Shifted Q e split c a b : G),hi⟩ =
        positivePoint Q split c (RingEquiv.refl _) (.inr 3) (a,b) := by
  rw [originalV2Shifted_positivePoint Q e split c h a b]
  exact ⟨_,originalPositivePoint_endpoint Q e h split c (RingEquiv.refl _) i (.inr 3) (a,b)⟩

def originalV2Opposite (a b : CoefficientField m) : pCore 2 (parabolic L S 1) :=
  (originalV2NumeratorEquiv Q e split c).symm
    (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 1 (by decide))
      (positiveChart Q split c (RingEquiv.refl _) (.inr 2) (a,b)))

theorem originalV2Opposite_endpoint (a b : CoefficientField m) :
    endpointMap Q e 1 (originalV2Opposite Q e split c a b) =
      positivePoint Q split c (RingEquiv.refl _) (.inr 2) (a,b) :=
  congrArg Subtype.val ((originalV2NumeratorEquiv Q e split c).apply_symm_apply _)

theorem originalV2Opposite_coordinates (a b : CoefficientField m) :
    originalV2Coordinates Q e split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk
        (originalV2Opposite Q e split (pinnedInput Q split c) a b))) = ![0,0,V2MiddleFieldLabel Q split c a,0] := by
  have he := congrArg (fun v : (V2Section Q split (pinnedInput Q split c)).numerator =>
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v)))
    ((originalV2NumeratorEquiv Q e split (pinnedInput Q split c)).apply_symm_apply
      (inclusion (positiveRoot_le_remainder Q split (pinnedInput Q split c) (.inr 2) 1 (by decide))
        (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 2) (a,b))))
  exact he.trans (pinnedV2_opposite_parameter Q split c a b)

theorem originalV2Opposite_positivePoint (h : HypothesisF11 L S) (a b : CoefficientField m) :
    (originalV2Opposite Q e split c a b : G) =
      originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 2) (a,b) := by
  have he : (originalV2Opposite Q e split c a b).val =
      (⟨originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 2) (a,b),
        (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 2) (a,b)).property⟩ :
        parabolic L S 1) := by
    apply (Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective
    change endpointMap Q e 1 _ = endpointMap Q e 1 _
    rw [originalV2Opposite_endpoint,originalPositivePoint_endpoint]
  exact congrArg Subtype.val he

theorem originalV2Opposite_endpoints (h : HypothesisF11 L S)
    (a b : CoefficientField m) (i : Fin 2) :
    ∃ hi : (originalV2Opposite Q e split c a b : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨(originalV2Opposite Q e split c a b : G),hi⟩ =
        positivePoint Q split c (RingEquiv.refl _) (.inr 2) (a,b) := by
  rw [originalV2Opposite_positivePoint Q e split c h a b]
  exact ⟨_,originalPositivePoint_endpoint Q e h split c (RingEquiv.refl _) i (.inr 2) (a,b)⟩

def originalV2NaturalPoint (σ : CoefficientField m ≃+* CoefficientField m)
    (p : Representation.SuzukiNatural.W m) :
    pCore 2 (parabolic L S 1) ⧸ originalT2 Q e split (pinnedInput Q split c) :=
  (originalV2Equiv Q e split (pinnedInput Q split c)).symm (V2NaturalPoint Q split c σ p)

theorem originalV2NaturalPoint_coordinates (σ : CoefficientField m ≃+* CoefficientField m)
    (p : Representation.SuzukiNatural.W m) :
    originalV2Coordinates Q e split (pinnedInput Q split c)
      (Additive.ofMul (originalV2NaturalPoint Q e split c σ p)) = p := by
  rw [originalV2Coordinates_apply]
  change V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
    ((originalV2Equiv Q e split (pinnedInput Q split c))
      ((originalV2Equiv Q e split (pinnedInput Q split c)).symm
        (V2NaturalPoint Q split c σ p)))) = p
  rw [MulEquiv.apply_symm_apply]
  exact V2NaturalPoint_coordinates Q split c σ p

theorem originalV2NaturalPoint_bijective (σ : CoefficientField m ≃+* CoefficientField m) :
    Function.Bijective (originalV2NaturalPoint Q e split c σ) :=
  (originalV2Equiv Q e split (pinnedInput Q split c)).symm.bijective.comp
    (V2NaturalPoint_bijective Q split c σ)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
open Subgroup ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

theorem originalV2Shifted_quotient (a b : CoefficientField m) :
    Q.q ⟨originalV2Shifted Q (originalMarkedIso Q) split c a b,
      parabolic_le_generated 1 (originalV2Shifted Q (originalMarkedIso Q) split c a b).val.property⟩ =
      positivePoint Q split c (RingEquiv.refl _) (.inr 3) (a,b) :=
  (originalMarkedIso_right_apply Q _).symm.trans
    (originalV2Shifted_endpoint Q (originalMarkedIso Q) split c a b)

theorem originalV2Opposite_quotient (a b : CoefficientField m) :
    Q.q ⟨originalV2Opposite Q (originalMarkedIso Q) split c a b,
      parabolic_le_generated 1 (originalV2Opposite Q (originalMarkedIso Q) split c a b).val.property⟩ =
      positivePoint Q split c (RingEquiv.refl _) (.inr 2) (a,b) :=
  (originalMarkedIso_right_apply Q _).symm.trans
    (originalV2Opposite_endpoint Q (originalMarkedIso Q) split c a b)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10


@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

/-- The exact commutator on the original positive-root representatives.
The coefficient still records both additive labels pending synchronization. -/
theorem original_shiftedSuzuki_right_commutator (h : HypothesisF11 L S)
    (σ : CoefficientField m ≃+* CoefficientField m) (a b y z : CoefficientField m) :
    (originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (y,z))⁻¹ *
      (originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 0) (a,b))⁻¹ *
      originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (y,z) *
      originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 0) (a,b) =
      originalPositivePoint Q e h split (pinnedInput Q split c) σ (.inl 1)
        ((reflectedLinearFieldLabel Q split (pinnedInput Q split c) σ).symm
          (a*V2MiddleFieldLabel Q split c y)) := by
  apply ReePresentation.sourceSylowMap_injective Q e h
  simp only [map_mul,map_inv,originalPositivePoint_image]
  have he : positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 0) (a,b) =
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := by
    change (1 : X ⧸ Q.D)⁻¹ * _ * 1 = _
    simp only [inv_one,one_mul,mul_one]
  rw [he]
  exact pinned_shiftedSuzuki_right_commutator Q split c σ a b y z

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
