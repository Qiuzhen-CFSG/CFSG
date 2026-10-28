module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSixHAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SynchronizedCommutators


/-!
# Synchronized source commutators on the original Sylow group

The full-overlap marking identifies the original Sylow group with the split
unipotent group. Pull back the synchronized positive-root charts along this
identification. Their images commute with both endpoint inclusions and,
for the canonical source quotient, are literally Q.q. Injectivity then
pulls the proved Section 10 commutator (10.8) back to the original carrier.

The original natural whole-Borel panel markings and odd-degree hypothesis
are retained. All parameters m >= 0, including the binary case, are covered;
no mixed-root equation or Section10Construction is assumed.
Source: Fong--Seitz II (1974), printed p.223, (10.8).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition

private theorem source_sylow_injective : Function.Injective (sylowMap Q e h) :=
  Q.tits.B.subtype_injective.comp
    (((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle).injective.comp
      (inclusion_injective _))

private def sourceSylowEquiv : S ≃* split.U :=
  (MonoidHom.ofInjective (source_sylow_injective Q e h)).trans
    (MulEquiv.subgroupCongr (sylow_range Q e h split))

/-- Synchronized positive-root points on the actual original Sylow carrier. -/
def originalSynchronizedPoint (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) : S :=
  (sourceSylowEquiv Q e h split).symm
    ⟨synchronizedPositivePoint Q split
      (originalSourceReeSixHData Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) i a,
      positiveRoot_le_unipotent Q split hm i
        (synchronizedPositiveChart Q split
          (originalSourceReeSixHData Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) i a).property⟩

/-- The literal full-overlap marking of each original synchronized root point. -/
theorem originalSynchronizedPoint_image (i : PositiveTables.Root) (a : PositiveTables.Parameter m i) :
    sylowMap Q e h (originalSynchronizedPoint Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁ i a) =
      synchronizedPositivePoint Q split
        (originalSourceReeSixHData Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) i a :=
  congrArg Subtype.val ((sourceSylowEquiv Q e h split).apply_symm_apply _)

/-- Every whole root retains both original endpoint inclusion squares. -/
theorem originalSynchronizedPoint_endpoints (i : PositiveTables.Root)
    (a : PositiveTables.Parameter m i) (k : Fin 2) :
    endpointMap Q e k
      ⟨originalSynchronizedPoint Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁ i a,
        (show S ≤ parabolic L S k from le_sup_right.trans le_sup_left)
          (originalSynchronizedPoint Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁ i a).property⟩ =
      synchronizedPositivePoint Q split
        (originalSourceReeSixHData Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) i a :=
  (endpoint_sylow Q e h k _).trans
    (originalSynchronizedPoint_image Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁ i a)

/-- The synchronized (10.8) is an equality on the original Sylow group. -/
theorem original_source_synchronized_ten_eight (a b y z : ReeF4.CoefficientField m) :
    let u := originalSynchronizedPoint Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    (u (.inr 3) (y,z))⁻¹ * (u (.inr 0) (a,b))⁻¹ *
      u (.inr 3) (y,z) * u (.inr 0) (a,b) = u (.inl 1) (a*y) := by
  let c := originalSourceReeSixHData Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
  have hs (x t : ReeF4.CoefficientField m) :
      synchronizedPositivePoint Q split c (.inr 0) (x,t) =
        (suzukiChart Q split (pinnedInput Q split c) (x,t) : X ⧸ Q.D) := by
    change (positiveRootEquiv Q split (pinnedInput Q split c) (.inr 0)
      (suzukiChart Q split (pinnedInput Q split c) (x,t)) : X ⧸ Q.D) = _
    simpa [positiveLift,positiveWord] using
      (positiveRootEquiv_apply Q split (pinnedInput Q split c) (.inr 0)
        (suzukiChart Q split (pinnedInput Q split c) (x,t)))
  apply source_sylow_injective Q e h
  simp only [map_mul,map_inv,originalSynchronizedPoint_image]
  change (synchronizedPositivePoint Q split c (.inr 3) (y,z))⁻¹ *
    (synchronizedPositivePoint Q split c (.inr 0) (a,b))⁻¹ *
    synchronizedPositivePoint Q split c (.inr 3) (y,z) *
    synchronizedPositivePoint Q split c (.inr 0) (a,b) =
      synchronizedPositivePoint Q split c (.inl 1) (a*y)
  rw [hs]
  exact synchronized_ten_eight Q split c a b y z

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {G : Type*} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition

/-- Every original synchronized root point follows literally Q.q. -/
theorem originalSynchronizedPoint_quotient (i : PositiveTables.Root)
    (a : PositiveTables.Parameter m i) :
    let u := originalSynchronizedPoint Q (originalMarkedIso Q) h split hm n hn m μ₀ T hB₀ μ₁ hB₁ i a
    Q.q ⟨u,(show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left).trans
      (parabolic_le_generated 1) u.property⟩ =
      synchronizedPositivePoint Q split
        (quotientSourceReeSixHData Q h split hm n hn m μ₀ T hB₀ μ₁ hB₁) i a := by
  let u := originalSynchronizedPoint Q (originalMarkedIso Q) h split hm n hn m μ₀ T hB₀ μ₁ hB₁ i a
  exact (originalMarkedIso_right_apply Q
    ⟨u,(show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left) u.property⟩).symm.trans
    (originalSynchronizedPoint_endpoints Q (originalMarkedIso Q) h split hm n hn m μ₀ T hB₀ μ₁ hB₁ i a 1)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
