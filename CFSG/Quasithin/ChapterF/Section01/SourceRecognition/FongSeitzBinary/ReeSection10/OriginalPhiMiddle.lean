module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiMiddleLines
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalPinned

/-!
# The original middle roots in the second Suzuki natural section

The two linear middle roots are transported into the Frattini subgroup of
original O₂(P₂). Their literal representatives agree with the existing
positive-root charts. Both ordered endpoint squares and the original Q.q
formula are retained, while their natural coordinates use the same additive
label. The four-root natural basis is also transported through the exact
Frattini/center quotient equivalence. A general marked isomorphism allows
the geometric source application, and every statement includes m = 0.

Source: Fong--Seitz II (1974), printed p.224, the basis before (10.11).
Field-label synchronization and the other Section 10 equations remain
separate reconstruction obligations.
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

def originalPhiPerpendicular (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    frattini (pCore 2 (parabolic L S 1)) :=
  (originalPhiNumeratorEquiv Q e split c).symm
    (inclusion (perpendicularLinear_le_phi Q split c) (positiveChart Q split c σ (.inl 3) a))

theorem originalPhiPerpendicular_endpoint
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    endpointMap Q e 1 (originalPhiPerpendicular Q e split c σ a).val.val =
      positivePoint Q split c σ (.inl 3) a :=
  congrArg Subtype.val ((originalPhiNumeratorEquiv Q e split c).apply_symm_apply _)

theorem originalPhiPerpendicular_coordinates
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    originalPhiCenterCoordinates Q e split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk
        (originalPhiPerpendicular Q e split (pinnedInput Q split c) σ a))) =
      ![0,phiPerpendicularFieldLabel Q split c σ a,0,0] := by
  have he := congrArg (fun v : (phiCenterSection Q split (pinnedInput Q split c)).numerator =>
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v)))
    ((originalPhiNumeratorEquiv Q e split (pinnedInput Q split c)).apply_symm_apply
      (inclusion (perpendicularLinear_le_phi Q split (pinnedInput Q split c))
        (positiveChart Q split (pinnedInput Q split c) σ (.inl 3) a)))
  exact he.trans (pinnedPhiCenter_perpendicular_fieldLabel Q split c σ a)

theorem originalPhiPerpendicular_positivePoint (h : HypothesisF11 L S)
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    ((originalPhiPerpendicular Q e split c σ a).val.val : G) =
      originalPositivePoint Q e h split c σ (.inl 3) a := by
  have he : (originalPhiPerpendicular Q e split c σ a).val.val =
      (⟨originalPositivePoint Q e h split c σ (.inl 3) a,
        (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q e h split c σ (.inl 3) a).property⟩ : parabolic L S 1) := by
    apply (Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective
    change endpointMap Q e 1 _ = endpointMap Q e 1 _
    rw [originalPhiPerpendicular_endpoint,originalPositivePoint_endpoint]
  exact congrArg Subtype.val he

theorem originalPhiPerpendicular_endpoints (h : HypothesisF11 L S)
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) (i : Fin 2) :
    ∃ hi : ((originalPhiPerpendicular Q e split c σ a).val.val : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨((originalPhiPerpendicular Q e split c σ a).val.val : G),hi⟩ =
        positivePoint Q split c σ (.inl 3) a := by
  rw [originalPhiPerpendicular_positivePoint Q e split c h σ a]
  exact ⟨_,originalPositivePoint_endpoint Q e h split c σ i (.inl 3) a⟩

def originalPhiNext (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    frattini (pCore 2 (parabolic L S 1)) :=
  (originalPhiNumeratorEquiv Q e split c).symm
    (inclusion (nextLinear_le_phi Q split c) (positiveChart Q split c σ (.inl 2) a))

theorem originalPhiNext_endpoint
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    endpointMap Q e 1 (originalPhiNext Q e split c σ a).val.val =
      positivePoint Q split c σ (.inl 2) a :=
  congrArg Subtype.val ((originalPhiNumeratorEquiv Q e split c).apply_symm_apply _)

theorem originalPhiNext_coordinates
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    originalPhiCenterCoordinates Q e split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk
        (originalPhiNext Q e split (pinnedInput Q split c) σ a))) =
      ![0,0,phiPerpendicularFieldLabel Q split c σ a,0] := by
  have he := congrArg (fun v : (phiCenterSection Q split (pinnedInput Q split c)).numerator =>
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v)))
    ((originalPhiNumeratorEquiv Q e split (pinnedInput Q split c)).apply_symm_apply
      (inclusion (nextLinear_le_phi Q split (pinnedInput Q split c))
        (positiveChart Q split (pinnedInput Q split c) σ (.inl 2) a)))
  exact he.trans (pinnedPhiCenter_next_fieldLabel Q split c σ a)

theorem originalPhiNext_positivePoint (h : HypothesisF11 L S)
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    ((originalPhiNext Q e split c σ a).val.val : G) =
      originalPositivePoint Q e h split c σ (.inl 2) a := by
  have he : (originalPhiNext Q e split c σ a).val.val =
      (⟨originalPositivePoint Q e h split c σ (.inl 2) a,
        (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q e h split c σ (.inl 2) a).property⟩ : parabolic L S 1) := by
    apply (Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective
    change endpointMap Q e 1 _ = endpointMap Q e 1 _
    rw [originalPhiNext_endpoint,originalPositivePoint_endpoint]
  exact congrArg Subtype.val he

theorem originalPhiNext_endpoints (h : HypothesisF11 L S)
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) (i : Fin 2) :
    ∃ hi : ((originalPhiNext Q e split c σ a).val.val : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨((originalPhiNext Q e split c σ a).val.val : G),hi⟩ =
        positivePoint Q split c σ (.inl 2) a := by
  rw [originalPhiNext_positivePoint Q e split c h σ a]
  exact ⟨_,originalPositivePoint_endpoint Q e h split c σ i (.inl 2) a⟩

/-- The four-root natural basis on the literal original Frattini quotient. -/
def originalPhiNaturalPoint (σ : CoefficientField m ≃+* CoefficientField m)
    (p : Representation.SuzukiNatural.W m) :
    frattini (pCore 2 (parabolic L S 1)) ⧸
      originalPhiCenterDenominator Q e split (pinnedInput Q split c) :=
  (originalPhiCenterEquiv Q e split (pinnedInput Q split c)).symm
    (phiNaturalPoint Q split c σ p)

theorem originalPhiNaturalPoint_coordinates
    (σ : CoefficientField m ≃+* CoefficientField m) (p : Representation.SuzukiNatural.W m) :
    originalPhiCenterCoordinates Q e split (pinnedInput Q split c)
      (Additive.ofMul (originalPhiNaturalPoint Q e split c σ p)) = p := by
  rw [originalPhiCenterCoordinates_apply]
  change phiCenterCoordinates Q split (pinnedInput Q split c)
    (Additive.ofMul ((originalPhiCenterEquiv Q e split (pinnedInput Q split c))
      ((originalPhiCenterEquiv Q e split (pinnedInput Q split c)).symm
        (phiNaturalPoint Q split c σ p)))) = p
  rw [MulEquiv.apply_symm_apply]
  exact phiNaturalPoint_coordinates Q split c σ p

theorem originalPhiNaturalPoint_bijective (σ : CoefficientField m ≃+* CoefficientField m) :
    Function.Bijective (originalPhiNaturalPoint Q e split c σ) :=
  (originalPhiCenterEquiv Q e split (pinnedInput Q split c)).symm.bijective.comp
    (phiNaturalPoint_bijective Q split c σ)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

theorem originalPhiPerpendicular_quotient
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    Q.q ⟨(originalPhiPerpendicular Q (originalMarkedIso Q) split c σ a).val.val,
      parabolic_le_generated 1
        (originalPhiPerpendicular Q (originalMarkedIso Q) split c σ a).val.val.property⟩ =
      positivePoint Q split c σ (.inl 3) a :=
  (originalMarkedIso_right_apply Q _).symm.trans
    (originalPhiPerpendicular_endpoint Q (originalMarkedIso Q) split c σ a)

theorem originalPhiNext_quotient
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    Q.q ⟨(originalPhiNext Q (originalMarkedIso Q) split c σ a).val.val,
      parabolic_le_generated 1
        (originalPhiNext Q (originalMarkedIso Q) split c σ a).val.val.property⟩ =
      positivePoint Q split c σ (.inl 2) a :=
  (originalMarkedIso_right_apply Q _).symm.trans
    (originalPhiNext_endpoint Q (originalMarkedIso Q) split c σ a)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

/-- The p.224 basis with original Omega parameters 1 and the same nonzero
linear parameter y on both middle roots. -/
theorem original_phi_source_basis (σ : CoefficientField m ≃+* CoefficientField m) :
    ∃ y s : CoefficientField m, y ≠ 0 ∧ s ≠ 0 ∧
      originalPhiCenterCoordinates Q e split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk
          (originalShiftedOmega Q e split (pinnedInput Q split c)
            (shiftedOmegaPoint Q split (pinnedInput Q split c) 1)))) = ![s,0,0,0] ∧
      originalPhiCenterCoordinates Q e split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk
          (originalPhiPerpendicular Q e split (pinnedInput Q split c) σ y))) = ![0,s,0,0] ∧
      originalPhiCenterCoordinates Q e split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk
          (originalPhiNext Q e split (pinnedInput Q split c) σ y))) = ![0,0,s,0] ∧
      originalPhiCenterCoordinates Q e split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk
          (originalOppositeOmega Q e split (pinnedInput Q split c) 1))) = ![0,0,0,s] := by
  obtain ⟨y,s,hy,hs,h₀,h₁,h₂,h₃⟩ := phi_source_basis Q split c σ
  refine ⟨y,s,hy,hs,?_,?_,?_,?_⟩
  · exact (originalShiftedOmega_fieldLabel Q e split (pinnedInput Q split c) 1).trans
      ((shiftedOmegaFieldLabel_coordinates Q split (pinnedInput Q split c) 1).symm.trans h₀)
  · exact (originalPhiPerpendicular_coordinates Q e split c σ y).trans
      ((pinnedPhiCenter_perpendicular_fieldLabel Q split c σ y).symm.trans h₁)
  · exact (originalPhiNext_coordinates Q e split c σ y).trans
      ((pinnedPhiCenter_next_fieldLabel Q split c σ y).symm.trans h₂)
  · exact (originalOppositeOmega_coordinates Q e split c 1).trans
      ((pinnedPhiCenter_oppositeOmega Q split c 1).symm.trans h₃)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
