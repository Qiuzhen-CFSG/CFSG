module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalV1Basis
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalV1Natural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearCharacteristic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalLinearDerived
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.Input
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.NaturalAlignment
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalRootLines
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalPinned
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalPhiMiddle
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalV2Middle
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiCommutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TorusAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.GaussEquations
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.GaussAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TauNormalization
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.NormalizerAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiMixedCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiFieldSynchronization
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixHApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.FullComparison

/-!
# Conditional Section 10 construction boundary

This module records the exact dependency boundary for Fong--Seitz II, §10.
`Section10Construction` contains the finite source charts and equation proofs
which the Section 10 owner must construct from `ReeSixHData`. Once those
source equations are supplied, the existing finite presentation theorem gives
the marked comparison on the same quotient, including the whole Borel and
both oriented parabolics. No model tag, abstract root-data wrapper, or
unproved source relation is used to manufacture the construction.

`ofOriginalSixH` is the checked transport of the already proved rank-one and
Cartan part of (6H) to this interface. The complete Section 10 relation package
remain explicit arguments; this theorem therefore makes no unconditional
claim about the original classification.

`AngularAssembly` reduces the positive-chart obligation to one literal angular
table. `AngularCoefficients` proves five of its ordered cases, retaining the
binary central coefficients; `ofRemainingAngular` consumes the other 23.
`TorusAssembly` constructs the native torus action, and
`TauNormalization` discharges both rank-one Gauss torus identifications. These bridges do
not turn the subgroup-level (6H) relations into the missing parameter table.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The source finite-equation output of the Section 10 reconstruction.

The dependencies are ordered so that later fields can refer to the same
literal chart, torus and Weyl lifts. This is intentionally a construction
bundle rather than an alternative presentation input: every field is one of
the public source interfaces consumed by `ReePresentation.FullComparison`.
-/
structure Section10Construction (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (n m : ℕ) where
  input : ReeSixHData Q split n m
  d : ReeF4.RootPresentationRecognition.SourcePositive.Charts Q split m
  E : ReeF4.RootPresentationRecognition.SourceAngular.Equations Q split d
  T : ReeF4.RootPresentationRecognition.SourceBorel.TorusData Q split d
  W : ReeF4.RootPresentationRecognition.SourceNormalizer.WeylData Q split d T
  R : ReeF4.RootPresentationRecognition.SourceSigned.Equations Q split d T W
  A : ReeF4.RootPresentationRecognition.Global.SourceGauss Q split d T W

variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (n m : ℕ)

/-- The checked conditional use of the Section 10 output on the same quotient.
The finite equation package is not weakened or replaced by an ambient model.
-/
def comparison
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      Q.standardAmalgam)
    (c : Section10Construction Q split n m) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (ReePresentation.orientedAmalgam m c.d.orientation) :=
  ReePresentation.comparison Q e split c.d c.T c.W c.E c.R c.A

include Q split m in
/-- The actual concrete Ree amalgam follows from the conditional source
construction, with either orientation retained. -/
theorem concrete_comparison
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      Q.standardAmalgam)
    (c : Section10Construction Q split n m) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m).reverse) := by
  exact ReePresentation.concrete_comparison Q e split c.d c.T c.W c.E c.R c.A

variable (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (n : ℕ) (hn : Odd n)
  (m₀ : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ ReeSource.originalPanelKernel (L := L) (S := S) 0) ≃*
    PSL2BinaryMatrixGroup n)
  (T₀ : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom =
    normalizer (T₀ : Set (PSL2BinaryMatrixGroup n)))
  (μ₁ : (parabolic L S 1 ⧸ ReeSource.originalPanelKernel (L := L) (S := S) 1) ≃*
    SuzukiMatrixGroup m₀)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m₀ : Set (SuzukiMatrixGroup m₀)))
  (s : ∀ i, RootReflection Q split i)
  (relations : SixHRelations Q split)

/-- Transport the proved source (6H) rank-one package to the lower
`ReeSixHData` interface. The relation propositions are retained literally as
arguments and are not inferred from the model equivalences. -/
def ofOriginalSixH
    (hm : rotationOrder Q = 8) :
    ReeSixHData Q split n m₀ := by
  let μL := faithfulModelMarking Q e h 0 μ₀
  let μS := faithfulModelMarking Q e h 1 μ₁
  have hμL : (quotientBorel Q 0).map μL.toMonoidHom =
      normalizer (T₀ : Set (PSL2BinaryMatrixGroup n)) :=
    faithfulModelMarking_borel Q e h 0 μ₀ (normalizer (T₀ : Set _)) hB₀
  have hμS : (quotientBorel Q 1).map μS.toMonoidHom =
      normalizer (SuzukiRootSubgroup m₀ : Set (SuzukiMatrixGroup m₀)) :=
    faithfulModelMarking_borel Q e h 1 μ₁ (normalizer (SuzukiRootSubgroup m₀ : Set _)) hB₁
  have hp := original_ree_sixH_package Q e h split hm n hn m₀ μ₀ T₀ hB₀ μ₁ hB₁ s
  have hcore : Q.tits.B.normalCore = ⊥ :=
    LinearThreePresentation.borel_core_eq_bot Q e h
  have hcartan := ree_cartan_card Q split hm n hn m₀ μL T₀ hμL μS hμS s hcore
  refine
    { rotation_eight := hm
      linear_degree_odd := hn
      linear := μL
      linearSylow := T₀
      linearBorel := hμL
      suzuki := μS
      suzukiBorel := hμS
      reflections := s
      common_field := hp.1
      hcore := hcore
      cartan_card := hcartan
      independent_root_centralizer := hp.2.2.1
      panel_kernel_centralizer := hp.2.2.2
      relations := relations }


/-- All finite source data assembled from the literal angular table.
The mixed positive table is the sole remaining equation input. -/
def Section10Construction.ofAngular {n m : ℕ}
    (c : ReeSixHData Q split n m)
    (E : OrderedRootPresentation.Equations
      (ReeF4.RootPresentationRecognition.AngularPresentation.table m)
      (synchronizedSourceRoot Q split c)) : Section10Construction Q split n m := by
  let d := synchronizedPositiveCharts Q split c E
  have hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a :=
    fun _ _ => rfl
  let T := synchronizedTorusData Q split c d hd
  let W := normalizedSynchronizedWeylData Q split c d T rfl rfl
  have hW : ∀ s, W.n s = sourceSimpleReflection Q split c s := fun _ => rfl
  exact
    { input := c
      d := d
      E := synchronizedPositiveCharts_angular Q split c E
      T := T
      W := W
      R := synchronizedSourceSigned_equations Q split c d T W hd hW
      A := normalizedSynchronizedSourceGauss Q split c d T W hd hW rfl }

/-- The five computed angular pairs are discharged internally; only the
remaining literal ordered equations are required from the Section 10 owner. -/
def Section10Construction.ofRemainingAngular {n m : ℕ}
    (c : ReeSixHData Q split n m)
    (E : RemainingAngularEquations Q split c) : Section10Construction Q split n m :=
  Section10Construction.ofAngular Q split c
    (synchronizedAngularEquations_of_remaining Q split c E)

/-! The final marked consumer can now be applied directly at the angular
equation boundary.  Keeping this as a separate theorem is useful for the
source assembly: it exposes the single remaining finite equation package and
does not hide it behind an existential or a model equivalence. -/

include Q split e in
theorem concrete_comparison_ofAngular {n m : ℕ}
    (c : ReeSixHData Q split n m)
    (E : OrderedRootPresentation.Equations
      (ReeF4.RootPresentationRecognition.AngularPresentation.table m)
      (synchronizedSourceRoot Q split c)) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m).reverse) := by
  exact concrete_comparison Q split n m e
    (Section10Construction.ofAngular Q split c E)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
