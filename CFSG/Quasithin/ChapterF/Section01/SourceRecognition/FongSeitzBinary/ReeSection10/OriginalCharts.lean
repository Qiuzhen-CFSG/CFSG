module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PositiveCharts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.Positive
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCoordinates

/-!
# Original marked applications of the Section 10 positive charts

The whole-Sylow equivalence from the same marked amalgam transports the
eight source charts and their unique twelve-parameter product coordinates
to the original S. Both ordered endpoint maps have exactly the prescribed
root and word images. The original generated-carrier specialization retains
literally Q.q on every representative. The general endpoint construction
also accepts the geometric marked isomorphism without changing maps.

The simple linear and corrected nonabelian Suzuki laws hold on these
original representatives for every m, including zero. No mixed exchange,
angular, torus, signed or Gauss equation is used to obtain these coordinates;
those equations and the full-model comparison remain reconstruction duties.

Source: Fong--Seitz II (1974), Section 10, pp.221--224 and230;
Carter (3G) ordered root products and the original F.1.1 marking.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.OrderedRootPresentation
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4 ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m) (σ : CoefficientField m ≃+* CoefficientField m)

/-- The twelve-parameter equivalence lifts through the same marked Sylow. -/
def originalPositiveCoordinates : PositiveParameters m ≃ S :=
  (positiveCoordinates Q split c σ).trans (ReePresentation.sourceSylowEquiv Q e h split).symm.toEquiv

/-- Every positive root point lifts to the original Sylow, before any
mixed-coordinate or whole-group recognition theorem. -/
def originalPositivePoint (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) : S :=
  (ReePresentation.sourceSylowEquiv Q e h split).symm
    ⟨positivePoint Q split c σ i a, positivePoint_mem_unipotent Q split c σ i a⟩

theorem originalPositivePoint_image (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) :
    sylowMap Q e h (originalPositivePoint Q e h split c σ i a) = positivePoint Q split c σ i a := by
  exact congrArg Subtype.val ((ReePresentation.sourceSylowEquiv Q e h split).apply_symm_apply _)

theorem originalPositivePoint_endpoint (k : Fin 2) (i : PositiveTables.Root)
    (a : PositiveTables.Parameter m i) :
    endpointMap Q e k
      ⟨originalPositivePoint Q e h split c σ i a,
        (show S ≤ parabolic L S k from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q e h split c σ i a).property⟩ =
      positivePoint Q split c σ i a := by
  rw [endpoint_sylow Q e h, originalPositivePoint_image]

theorem originalPositiveCoordinates_image (a : PositiveParameters m) :
    sylowMap Q e h (originalPositiveCoordinates Q e h split c σ a) =
      word (PositiveTables.Parameter m) (positivePoint Q split c σ) (List.ofFn positiveIndex) a := by
  change (ReePresentation.sourceSylowEquiv Q e h split
    ((ReePresentation.sourceSylowEquiv Q e h split).symm (positiveCoordinates Q split c σ a)) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply, positiveCoordinates_apply]

/-- Both ordered endpoint inclusions retain the same twelve-parameter word. -/
theorem originalPositiveCoordinates_endpoint (k : Fin 2) (a : PositiveParameters m) :
    endpointMap Q e k
      ⟨originalPositiveCoordinates Q e h split c σ a,
        (show S ≤ parabolic L S k from le_sup_right.trans le_sup_left)
          (originalPositiveCoordinates Q e h split c σ a).property⟩ =
      word (PositiveTables.Parameter m) (positivePoint Q split c σ) (List.ofFn positiveIndex) a := by
  rw [endpoint_sylow Q e h, originalPositiveCoordinates_image]

theorem originalPositivePoint_pair_mul (i : Fin 4) (a b : CoefficientField m) :
    originalPositivePoint Q e h split c σ (.inl i) a *
      originalPositivePoint Q e h split c σ (.inl i) b =
        originalPositivePoint Q e h split c σ (.inl i) (a+b) := by
  apply ReePresentation.sourceSylowMap_injective Q e h
  rw [map_mul, originalPositivePoint_image, originalPositivePoint_image,
    originalPositivePoint_image, positivePoint_pair_mul]

theorem originalPositivePoint_quartet_mul (i : Fin 4) (a b u v : CoefficientField m) :
    originalPositivePoint Q e h split c σ (.inr i) (a,b) *
      originalPositivePoint Q e h split c σ (.inr i) (u,v) =
        originalPositivePoint Q e h split c σ (.inr i) (a+u,b+v+titsEnd m a*u) := by
  apply ReePresentation.sourceSylowMap_injective Q e h
  rw [map_mul, originalPositivePoint_image, originalPositivePoint_image,
    originalPositivePoint_image, positivePoint_quartet_mul]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.OrderedRootPresentation
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4 ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {n m : ℕ} (c : ReeSixHData Q split n m) (σ : CoefficientField m ≃+* CoefficientField m)

/-- Original root representatives retain precisely the quotient map Q.q. -/
theorem originalPositivePoint_quotient (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) :
    Q.q ⟨originalPositivePoint Q (originalMarkedIso Q) h split c σ i a,
      parabolic_le_generated 0
        ((show S ≤ parabolic L S 0 from le_sup_right.trans le_sup_left)
          (originalPositivePoint Q (originalMarkedIso Q) h split c σ i a).property)⟩ =
      positivePoint Q split c σ i a :=
  (originalMarkedIso_left_apply Q _).symm.trans
    (originalPositivePoint_endpoint Q (originalMarkedIso Q) h split c σ 0 i a)

/-- The unique full-Sylow coordinates retain precisely the original quotient. -/
theorem originalPositiveCoordinates_quotient (a : PositiveParameters m) :
    Q.q ⟨originalPositiveCoordinates Q (originalMarkedIso Q) h split c σ a,
      parabolic_le_generated 0
        ((show S ≤ parabolic L S 0 from le_sup_right.trans le_sup_left)
          (originalPositiveCoordinates Q (originalMarkedIso Q) h split c σ a).property)⟩ =
      word (PositiveTables.Parameter m) (positivePoint Q split c σ) (List.ofFn positiveIndex) a :=
  (originalMarkedIso_left_apply Q _).symm.trans
    (originalPositiveCoordinates_endpoint Q (originalMarkedIso Q) h split c σ 0 a)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
