module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.FieldMarking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.ModuleApplication

/-!
# The source cubic basis in the literal triality coefficient application

The compatible field marking proves that a nonfixed scalar has basis
1, θ, θ² over the actual fixed field. This removes the independent spanning
premise of ModuleStage. The earlier module equations below still include the
three matrix calculations (9.27), unknown coefficients f and g, and the
torus covariance. They must be constructed from the two source modules;
this module does not assume their later normalized coefficients.

The resulting positive data and original/geometric range applications use
the same quotient, root pinnings, fixed-field inclusion and endpoint marking.
The signed Bruhat application retains the full Borel and Q.q, with mixed
torus equations still explicit.

Source: Fong--Seitz II, printed p.219, the cubic basis immediately before
(9.27), followed by (9.27)--(9.35).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
open PinnedApplication
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
section Equations
variable (p : RankOnePair σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ) (θ : F)

/-- The earlier matrix equations in the chosen cubic coordinate. The spanning
property is proved from the source field, rather than supplied as a field. -/
structure CubicModuleEquations where
  f : F → F → K
  g : F → K → K
  τ : K ≃+* K
  highest_injective : Function.Injective (p.longOrbit 2)
  short0_long1 : ∀ a b, Commute (p.s 0 a) (p.l 1 b)
  short0_long2 : ∀ a b, Commute (p.s 0 a) (p.l 2 b)
  long0_short1 : ∀ a b, Commute (p.l 0 a) (p.s 1 b)
  long0_short2 : ∀ a b, Commute (p.l 0 a) (p.s 2 b)
  long0_long2 : ∀ a b, Commute (p.l 0 a) (p.l 2 b)
  short1_long1 : ∀ a b, Commute (p.s 1 a) (p.l 1 b)
  short1_long2 : ∀ a b, Commute (p.s 1 a) (p.l 2 b)
  short2_long1 : ∀ a b, Commute (p.s 2 a) (p.l 1 b)
  short2_long2 : ∀ a b, Commute (p.s 2 a) (p.l 2 b)
  long1_long2 : ∀ a b, Commute (p.l 1 a) (p.l 2 b)
  basis_pairing : ∀ (a : F) (b : K) (i : Fin 3),
    rightCommutator (p.s 2 (b.val*θ^i.val)) (p.s 0 a) =
      p.l 1 (e.trace (a*(b.val*θ^i.val)))
  short_short : ∀ a b, rightCommutator (p.s 1 b) (p.s 0 a) =
    p.s 2 (σ a * σ (σ b) + σ (σ a) * σ b) *
      p.l 1 (e.trace (σ a * σ (σ a) * b)) * p.l 2 (f a b)
  mixed : ∀ a b, rightCommutator (p.l 0 b) (p.s 0 a) =
    p.s 1 (a*b.val) * p.s 2 (σ a * σ (σ a) * b.val) *
      p.l 1 (e.norm a * b) * p.l 2 (g a b)
  long_twisted : ∀ a b, rightCommutator (p.l 1 b) (p.l 0 a) = p.l 2 (b * τ a)
  covariance : CoefficientCovariance e g

namespace CubicModuleEquations
variable {p e θ} (d : CubicModuleEquations p e θ) [Finite F]

/-- Supply the cubic expansion required by the existing coefficient proof. -/
def moduleStage (hθ : σ θ ≠ θ) : ModuleStage p e where
  θ := θ
  spans := scalarMarking_spans_of_nonfixed e θ hθ
  f := d.f
  g := d.g
  τ := d.τ
  highest_injective := d.highest_injective
  short0_long1 := d.short0_long1
  short0_long2 := d.short0_long2
  long0_short1 := d.long0_short1
  long0_short2 := d.long0_short2
  long0_long2 := d.long0_long2
  short1_long1 := d.short1_long1
  short1_long2 := d.short1_long2
  short2_long1 := d.short2_long1
  short2_long2 := d.short2_long2
  long1_long2 := d.long1_long2
  basis_pairing := d.basis_pairing
  short_short := d.short_short
  mixed := d.mixed
  long_twisted := d.long_twisted
  covariance := d.covariance

include d in
/-- The full trace pairing follows from the three matrix calculations and
the cubic field; no separate spanning hypothesis remains. -/
theorem lower (hθ : σ θ ≠ θ) :
    ∀ a b, rightCommutator (p.s 2 b) (p.s 0 a) = p.l 1 (e.trace (a*b)) :=
  (d.moduleStage hθ).lower

end CubicModuleEquations
end Equations

namespace FieldMarkingApplication
variable [Finite F] {n : ℕ} {hn : 0 < n}
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p)
  (base : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
  (e : ScalarMarking (binaryParameters n hn) σ)
  (hm : rotationOrder Q = 6) (θ : F) (hθ : σ θ ≠ θ)
  (d : CubicModuleEquations p e θ) (orientation : Bool)
  (placement : ∀ A, A ∈ orderedRoots Q split orientation 6 ↔ ∃ i, (rawRoots p).ranges i = A)

/-- The actual positive-root consumer with the source cubic expansion discharged. -/
def positiveData : TrialityPresentation.PositiveRootData Q split n hn σ :=
  ModuleApplication.positiveData Q split p w base e hm (d.moduleStage hθ) orientation placement

/-- Keep the supplied original/geometric amalgam marking and its actual S image. -/
theorem nativeHom_range_marked {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split p w base e hm θ hθ d orientation placement).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  ModuleApplication.nativeHom_range_marked Q split p w base e hm (d.moduleStage hθ)
    orientation placement marking h

/-- The signed Bruhat consumer retains the same field, roots and full Borel.
Its mixed torus equations are a remaining source obligation. -/
def bruhatData {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S)
    (t : (p.signedRoots e).TorusRelations) :
    TrialityPresentation.BruhatRootData
      (positiveData Q split p w base e hm θ hθ d orientation placement) :=
  ModuleApplication.bruhatData Q split p w base e hm (d.moduleStage hθ)
    orientation placement marking h t

include split w base hm θ hθ d orientation placement in
/-- The quotient equation still uses the original map Q.q and full Q.tits.B. -/
theorem quotient_bruhat {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S)
    (t : (p.signedRoots e).TorusRelations) (x : X) :
    ∃ (u v : X ⧸ Q.D) (a : Bool) (k : ℕ),
      u ∈ Q.tits.B ∧ v ∈ Q.tits.B ∧ k ≤ 6 ∧
      Q.q x = u * (p.signedRoots e).alternating a k * v :=
  (bruhatData Q split p w base e hm θ hθ d orientation placement marking h t).source_bruhat (Q.q x)

/-- For the original numerator, the positive image is the original S image
under its quotient map, without an assumed universal-to-original descent. -/
theorem nativeHom_range_original
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h₀ : HypothesisF11 L S) (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (p₀ : RankOnePair σ ((generated L S) ⧸ Q₀.D)) (w₀ : WeylPlacement Q₀ p₀)
    (base₀ : (p₀.longOrbit 0).range = simpleRoot Q₀ split₀ (w₀.indices 1))
    (e₀ : ScalarMarking (binaryParameters n hn) σ) (hm₀ : rotationOrder Q₀ = 6)
    (θ₀ : F) (hθ₀ : σ θ₀ ≠ θ₀) (d₀ : CubicModuleEquations p₀ e₀ θ₀) (orientation₀ : Bool)
    (placement₀ : ∀ A, A ∈ orderedRoots Q₀ split₀ orientation₀ 6 ↔
      ∃ i, (rawRoots p₀).ranges i = A) :
    (positiveData Q₀ split₀ p₀ w₀ base₀ e₀ hm₀ θ₀ hθ₀ d₀ orientation₀ placement₀).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q₀.q :=
  TrialityPresentation.nativeHom_range_original h₀ Q₀ split₀
    (positiveData Q₀ split₀ p₀ w₀ base₀ e₀ hm₀ θ₀ hθ₀ d₀ orientation₀ placement₀)

end FieldMarkingApplication
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
