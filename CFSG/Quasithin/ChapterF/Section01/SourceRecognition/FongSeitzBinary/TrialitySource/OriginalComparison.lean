module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.SourceFieldApplication

/-!
# Original quotient application of reconstructed triality recognition

Apply the full source-field and signed-root reconstruction to the original
generated-group quotient. The existing marked presentation supplies one
ambient equivalence, its entire Borel restriction and both endpoint maps.
The representative formulas retain the literal Q.q and both inclusion
squares on the complete original overlap. The native positive image is the
original S image. Neither source relation certificates nor descent from an
unrelated universal completion are required.

The exact earlier split geometry, actual local models and 6E(b) structural
row remain explicit. Both orientations and all positive binary exponents
are retained. Source: Fong--Seitz II §9B; DGS Theorem D; AS F.1.1--12.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.OriginalComparison
variable {G F K₀ : Type*} [Group G] [Field F] [Finite F] [CharP F 2] [Field K₀] [Finite K₀]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (indices : Fin 2 ≃ Fin 2)
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃* PSL(2,K₀))
  (hm : rotationOrder Q = 6) (row : StructuralRow Q split (indices 0) (indices 1))
  {n : ℕ} {hn : 0 < n} (hcard : Nat.card F = (2^n)^3) (hsmall : Nat.card K₀ = 2^n)

/-- Construct every root and torus equation on the original generated-group quotient. -/
def rootData : TrialityPresentation.RootData Q split n hn
    (SourceFieldApplication.sourceFrobenius F n) (indices 0) :=
  SourceFieldApplication.markedRootData Q split indices hVi hVj μi μj hm row hcard hsmall
    (originalMarkedIso Q) h
local notation "d" => rootData (hn := hn) h Q split indices hVi hVj μi μj hm row hcard hsmall

/-- Full original comparison with the actual quotient projection. -/
def comparison := TrialityPresentation.originalComparison Q (d)

@[simp] theorem comparison_left_apply (a : parabolic L S 0) :
    ((comparison (hn := hn) h Q split indices hVi hVj μi μj hm row hcard hsmall).left a : BinaryCarrier n hn) =
      (d).bruhat.quotientEquiv (Q.q ⟨a,parabolic_le_generated 0 a.property⟩) :=
  TrialityPresentation.originalComparison_left_apply Q (d) a

@[simp] theorem comparison_middle_apply (a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison (hn := hn) h Q split indices hVi hVj μi μj hm row hcard hsmall).middle a : BinaryCarrier n hn) =
      (d).bruhat.quotientEquiv (Q.q ⟨a,parabolic_le_generated 0 a.property.1⟩) :=
  TrialityPresentation.originalComparison_middle_apply Q (d) a

@[simp] theorem comparison_right_apply (a : parabolic L S 1) :
    ((comparison (hn := hn) h Q split indices hVi hVj μi μj hm row hcard hsmall).right a : BinaryCarrier n hn) =
      (d).bruhat.quotientEquiv (Q.q ⟨a,parabolic_le_generated 1 a.property⟩) :=
  TrialityPresentation.originalComparison_right_apply Q (d) a

/-- Both inclusion squares hold on every element of the whole original overlap. -/
theorem endpoint_squares (a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := comparison (hn := hn) h Q split indices hVi hVj μi μj hm row hcard hsmall
    c.left ⟨a,a.property.1⟩ = (TrialityPresentation.flagAmalgam n hn (indices 0)).left (c.middle a) ∧
    c.right ⟨a,a.property.2⟩ = (TrialityPresentation.flagAmalgam n hn (indices 0)).right (c.middle a) :=
  ⟨(comparison (hn := hn) h Q split indices hVi hVj μi μj hm row hcard hsmall).left_commutes a,
    (comparison (hn := hn) h Q split indices hVi hVj μi μj hm row hcard hsmall).right_commutes a⟩

/-- The complete original S image under Q.q is the native positive image. -/
theorem nativeHom_range_original : (d).positive.nativeHom.range =
    (S.subgroupOf (generated L S)).map Q.q :=
  TrialityPresentation.nativeHom_range_original h Q split (d).positive

/-- The complete Borel, not only its unipotent part, is preserved. -/
theorem full_borel : Q.tits.B.map (d).bruhat.quotientEquiv.toMonoidHom =
    Parabolics.borel (binaryParameters n hn) := (d).bruhat.quotientEquiv_borel

include h Q split indices hVi hVj μi μj hm row hcard hsmall hn in
/-- Actual original source application of the completed marked presentation. -/
theorem concreteComparison : Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) :=
  (d).concreteComparison (originalMarkedIso Q)
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.OriginalComparison
