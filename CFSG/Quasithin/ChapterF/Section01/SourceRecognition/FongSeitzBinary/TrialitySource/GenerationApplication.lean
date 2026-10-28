module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.Generation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.SignedApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.CoefficientPolarization
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.BruhatCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.NormalGeneration

/-!
# Ambient signed generation on the literal source quotient

The constructed signed subgroup is the normal closure of the same source U.
The original F.1.1 Sylow and local maximality hypotheses imply that this
normal closure is the whole marked quotient, including the nonperfect q=2
case. Thus the triality Bruhat consumer needs no additional generation
certificate. Its input torus equations, compatible pinnings, coefficient
stage and Weyl placements are still source reconstruction obligations.

Both original and geometric markings use the supplied isomorphism to
Q.standardAmalgam. The quotient map Q.q, the full Borel and both endpoint
maps remain unchanged; no descent from a universal numerator is assumed.
Source: Fong--Seitz I, ambient normal-generation hypothesis; II §9B;
DGS Theorem D, printed p.224; AS F.1.1--3.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.PinnedApplication
variable {F : Type*} [Field F] [CharP F 2] [Finite F] {σ : F ≃+* F}
  {X : Type*} [Group X] {P : Fin 2 → Subgroup X} {n : ℕ} {hn : 0 < n}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (p : RankOnePair σ (X ⧸ Q.D)) (e : ScalarMarking (binaryParameters n hn) σ)
  (orientation : Bool) (hm : rotationOrder Q = 6)
  (placement : ∀ A, A ∈ orderedRoots Q split orientation 6 ↔ ∃ i, (rawRoots p).ranges i = A)
  (c : (rawRoots p).CoefficientStage e) (w : WeylPlacement Q p)
  {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (marking : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam) (h : HypothesisF11 L S)

include hm placement c w marking h in
/-- Normal generation is discharged on this very quotient, including q=2. -/
theorem signedClosure_eq_top : (p.signedRoots e).signedClosure = ⊤ := by
  rw [w.signedClosure_eq_unipotentClosure Q split p e
    (positiveData Q split p e orientation hm placement c).positive]
  exact A2Source.unipotent_normalClosure_eq_top Q marking h split

/-- The full presentation's generation field follows from the original source
hypotheses. The mixed torus equations remain explicit. -/
def bruhatData (t : (p.signedRoots e).TorusRelations) :
    TrialityPresentation.BruhatRootData (positiveData Q split p e orientation hm placement c) where
  signed := signedData Q split p e orientation hm placement c
  weyl := weylRelations Q split p e orientation hm placement c
  torus := t
  generates := signedClosure_eq_top Q split p e orientation hm placement c w marking h

include split orientation hm placement c w marking h in
/-- The literal quotient has the complete source-Borel Bruhat cover once the
remaining torus equations are proved. -/
theorem source_bruhat (t : (p.signedRoots e).TorusRelations) (y : X ⧸ Q.D) :
    ∃ (u v : X ⧸ Q.D) (a : Bool) (k : ℕ),
      u ∈ Q.tits.B ∧ v ∈ Q.tits.B ∧ k ≤ 6 ∧
      y = u * (p.signedRoots e).alternating a k * v :=
  (bruhatData Q split p e orientation hm placement c w marking h t).source_bruhat y

include split orientation hm placement c w marking h in
/-- Keep every original representative under the unchanged quotient projection. -/
theorem quotient_bruhat (t : (p.signedRoots e).TorusRelations) (x : X) :
    ∃ (u v : X ⧸ Q.D) (a : Bool) (k : ℕ),
      u ∈ Q.tits.B ∧ v ∈ Q.tits.B ∧ k ≤ 6 ∧
      Q.q x = u * (p.signedRoots e).alternating a k * v :=
  source_bruhat Q split p e orientation hm placement c w marking h t (Q.q x)

omit [Finite F] in
/-- Each chosen simple Weyl lift lies in its literal endpoint, for either orientation. -/
theorem weyl_endpoint (i : Fin 2) :
    ∃ x : P (w.indices i), Q.q x = (w.lift i : X ⧸ Q.D) ∧
      (Q.endpointEquiv (w.indices i) x : X ⧸ Q.D) = (w.lift i : X ⧸ Q.D) := by
  have hv : (w.lift i : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple (w.indices i)} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ (w.lift i) (w.simple i))
  let y : Q.tits.standardParabolic {Q.simple (w.indices i)} := ⟨w.lift i,hv⟩
  refine ⟨(Q.endpointEquiv (w.indices i)).symm y, ?_, ?_⟩
  · simpa only [← MarkedQuotient.endpointEquiv_apply] using
      congrArg Subtype.val ((Q.endpointEquiv (w.indices i)).apply_symm_apply y)
  · exact congrArg Subtype.val ((Q.endpointEquiv (w.indices i)).apply_symm_apply y)

/-- The same generation theorem for the original generated numerator. -/
theorem original_signedClosure_eq_top
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h₀ : HypothesisF11 L S)
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (p₀ : RankOnePair σ ((generated L S) ⧸ Q₀.D))
    (e₀ : ScalarMarking (binaryParameters n hn) σ)
    (orientation₀ : Bool) (hm₀ : rotationOrder Q₀ = 6)
    (placement₀ : ∀ A, A ∈ orderedRoots Q₀ split₀ orientation₀ 6 ↔
      ∃ i, (rawRoots p₀).ranges i = A)
    (c₀ : (rawRoots p₀).CoefficientStage e₀) (w₀ : WeylPlacement Q₀ p₀) :
    (p₀.signedRoots e₀).signedClosure = ⊤ :=
  signedClosure_eq_top Q₀ split₀ p₀ e₀ orientation₀ hm₀ placement₀ c₀ w₀
    (originalMarkedIso Q₀) h₀

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.PinnedApplication

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.UnnormalizedApplication
open PinnedApplication
variable {F : Type*} [Field F] [CharP F 2] [Finite F] {σ : F ≃+* F}
  {X : Type*} [Group X] {P : Fin 2 → Subgroup X} {n : ℕ} {hn : 0 < n}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (p : RankOnePair σ (X ⧸ Q.D)) (e : ScalarMarking (binaryParameters n hn) σ)
  (orientation : Bool) (hm : rotationOrder Q = 6)
  (placement : ∀ A, A ∈ orderedRoots Q split orientation 6 ↔ ∃ i, (rawRoots p).ranges i = A)
  (d : (rawRoots p).UnnormalizedStage e)

/-- The literal positive data are constructed without assuming polarization. -/
def positiveData : TrialityPresentation.PositiveRootData Q split n hn σ :=
  PinnedApplication.positiveData Q split p e orientation hm placement d.toCoefficientStage

/-- The derived coefficient equations retain the exact original/geometric S image. -/
theorem nativeHom_range_marked {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split p e orientation hm placement d).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  (positiveData Q split p e orientation hm placement d).nativeHom_range_marked marking h

/-- Both polarization and ambient generation are proved in this application;
the explicit mixed torus equations remain to be constructed. -/
def bruhatData (w : WeylPlacement Q p) {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S)
    (t : (p.signedRoots e).TorusRelations) :
    TrialityPresentation.BruhatRootData (positiveData Q split p e orientation hm placement d) :=
  PinnedApplication.bruhatData Q split p e orientation hm placement d.toCoefficientStage w marking h t

/-- The original numerator keeps Q.q after the coefficient reconstruction. -/
theorem nativeHom_range_original
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h₀ : HypothesisF11 L S) (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (p₀ : RankOnePair σ ((generated L S) ⧸ Q₀.D))
    (e₀ : ScalarMarking (binaryParameters n hn) σ)
    (orientation₀ : Bool) (hm₀ : rotationOrder Q₀ = 6)
    (placement₀ : ∀ A, A ∈ orderedRoots Q₀ split₀ orientation₀ 6 ↔
      ∃ i, (rawRoots p₀).ranges i = A)
    (d₀ : (rawRoots p₀).UnnormalizedStage e₀) :
    (positiveData Q₀ split₀ p₀ e₀ orientation₀ hm₀ placement₀ d₀).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q₀.q :=
  TrialityPresentation.nativeHom_range_original h₀ Q₀ split₀
    (positiveData Q₀ split₀ p₀ e₀ orientation₀ hm₀ placement₀ d₀)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.UnnormalizedApplication
