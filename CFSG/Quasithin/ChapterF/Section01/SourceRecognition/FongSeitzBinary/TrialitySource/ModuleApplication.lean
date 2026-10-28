module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.ModuleCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.GenerationApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.NonabelianRadicals

/-!
# Module-stage triality application on the same quotient

The actual two Weyl lifts identify the first and highest conjugated long
roots with the canonical hexagon roots. Their disjointness follows from
reduced Weyl lengths, for either orientation; it is not a coefficient
uniqueness certificate. This supplies the separation used to determine
(9.30) in ModuleCoefficients.

The resulting PositiveRootData retains Q.q, the original/geometric S image,
and the supplied marking to Q.standardAmalgam. The signed generation and
Bruhat consumer reuse those same pinnings, quotient and full Borel. The
mixed torus relations remain explicit, as do the earlier module equations,
compatible pinnings, simple-root identification and Weyl placements.

Source: Fong--Seitz I (6E)(b), II (9.27)–(9.35); Carter 2.5.10–17;
DGS Theorem D, printed p.224. The rootAt conventions are right conjugation,
whereas the pinning's Weyl automorphisms use left conjugation; their
involutions justify the conversion below.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.ModuleApplication
open PinnedApplication
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}

private theorem long_one_range (p : RankOnePair σ Y) :
    (p.longOrbit 1).range = rightConjugate (p.longOrbit 0).range p.dihedral.a := by
  ext x
  change (∃ t, p.dihedral.A (p.longOrbit 0 t) = x) ↔ ∃ t, p.longOrbit 0 t = p.dihedral.A x
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,(p.dihedral.A_A _).symm⟩
  · rintro ⟨t,ht⟩
    exact ⟨t, by rw [ht, p.dihedral.A_A]⟩

private theorem long_two_range (p : RankOnePair σ Y) :
    (p.longOrbit 2).range = rightConjugate (p.longOrbit 1).range p.dihedral.b := by
  ext x
  change (∃ t, p.dihedral.B (p.longOrbit 1 t) = x) ↔ ∃ t, p.longOrbit 1 t = p.dihedral.B x
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,(p.dihedral.B_B _).symm⟩
  · rintro ⟨t,ht⟩
    exact ⟨t, by rw [ht, p.dihedral.B_B]⟩

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p)
  (base : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))

include base in
/-- The first conjugated long root retains its canonical right Weyl word. -/
theorem long_one_rootAt :
    (p.longOrbit 1).range = rootAt Q split (w.indices 1) (Q.simple (w.indices 0)) := by
  rw [long_one_range, base, ← w.short]
  exact (rootAt_eq Q split (w.indices 1) _ (w.lift 0) (w.simple 0)).symm

include base in
/-- The highest long root uses the same two selected source lifts. -/
theorem long_two_rootAt :
    (p.longOrbit 2).range =
      rootAt Q split (w.indices 1) (Q.simple (w.indices 0)*Q.simple (w.indices 1)) := by
  rw [long_two_range, long_one_rootAt Q split p w base, ← w.long]
  exact rootAt_right Q split (w.indices 1) _ _ (w.lift 1) (w.simple 1)

include base in
/-- The disjointness needed to compare source coefficients follows from the
canonical hexagon roots, in either source orientation. -/
theorem long_ranges_disjoint (hm : rotationOrder Q = 6) :
    Disjoint (p.longOrbit 1).range (p.longOrbit 2).range := by
  rw [long_one_rootAt Q split p w base, long_two_rootAt Q split p w base]
  exact exchanged_roots_disjoint Q split hm (w.indices 1) (w.indices 0)
    (w.indices.injective.ne (by decide))

variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)
  (hm : rotationOrder Q = 6) (d : ModuleStage p e)

/-- Discharge the geometric separation premise before entering the existing
coefficient and polarization chain on this exact quotient. -/
def coefficientStage : (rawRoots p).UnnormalizedStage e :=
  d.toUnnormalizedStage (long_ranges_disjoint Q split p w base hm)

variable [Finite F] (orientation : Bool)
  (placement : ∀ A, A ∈ orderedRoots Q split orientation 6 ↔ ∃ i, (rawRoots p).ranges i = A)

/-- PositiveRootData on the literal quotient, with the later source coefficient
equations and polarization proved from ModuleStage. -/
def positiveData : TrialityPresentation.PositiveRootData Q split n hn σ :=
  UnnormalizedApplication.positiveData Q split p e orientation hm placement
    (coefficientStage Q split p w base e hm d)

/-- The original/geometric S image is retained through the supplied amalgam
isomorphism, without a universal-to-original descent. -/
theorem nativeHom_range_marked {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split p w base e hm d orientation placement).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  (positiveData Q split p w base e hm d orientation placement).nativeHom_range_marked marking h

/-- The existing signed and generation constructors apply after the module-stage
coefficient reconstruction. The mixed torus source equations remain explicit. -/
def bruhatData {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S)
    (t : (p.signedRoots e).TorusRelations) :
    TrialityPresentation.BruhatRootData (positiveData Q split p w base e hm d orientation placement) :=
  UnnormalizedApplication.bruhatData Q split p e orientation hm placement
    (coefficientStage Q split p w base e hm d) w marking h t

include split w base hm d orientation placement in
/-- The quotient map Q.q and full source Borel are unchanged in the Bruhat cover. -/
theorem quotient_bruhat {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S)
    (t : (p.signedRoots e).TorusRelations) (x : X) :
    ∃ (u v : X ⧸ Q.D) (a : Bool) (k : ℕ),
      u ∈ Q.tits.B ∧ v ∈ Q.tits.B ∧ k ≤ 6 ∧
      Q.q x = u * (p.signedRoots e).alternating a k * v :=
  (bruhatData Q split p w base e hm d orientation placement marking h t).source_bruhat (Q.q x)

/-- For the original generated numerator the positive image is exactly the
image of its original S under the original quotient map. -/
theorem nativeHom_range_original
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h₀ : HypothesisF11 L S) (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (p₀ : RankOnePair σ ((generated L S) ⧸ Q₀.D)) (w₀ : WeylPlacement Q₀ p₀)
    (base₀ : (p₀.longOrbit 0).range = simpleRoot Q₀ split₀ (w₀.indices 1))
    (e₀ : ScalarMarking (binaryParameters n hn) σ) (hm₀ : rotationOrder Q₀ = 6)
    (d₀ : ModuleStage p₀ e₀) (orientation₀ : Bool)
    (placement₀ : ∀ A, A ∈ orderedRoots Q₀ split₀ orientation₀ 6 ↔
      ∃ i, (rawRoots p₀).ranges i = A) :
    (positiveData Q₀ split₀ p₀ w₀ base₀ e₀ hm₀ d₀ orientation₀ placement₀).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q₀.q :=
  TrialityPresentation.nativeHom_range_original h₀ Q₀ split₀
    (positiveData Q₀ split₀ p₀ w₀ base₀ e₀ hm₀ d₀ orientation₀ placement₀)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.ModuleApplication
