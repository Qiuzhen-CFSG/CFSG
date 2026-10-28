module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.FullApplication
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The cubic source field and full triality reconstruction

Use the field of the earlier cubic rank-one model as the source extension,
and define its q-power Frobenius. Its cardinality constructs an intertwining
extension equivalence. The final fixed-field marking is the restriction of
this same equivalence. The earlier small-field model is transported as a
whole into that actual fixed subfield before the source pinning and module
comparison are constructed. Thus no scalar marking or compatible field
inclusion is a remaining input to the full marked comparison.

The local models here are actual group isomorphisms, accompanied by the
source structural row and remainder-to-kernel containments on the same
quotient. Cardinalities alone are not used to infer the row or mixed laws.
Every positive binary exponent, including q=2 and q=4, and both orientations
are included. Final source assembly retains the earlier row-selection inputs.
Source: Fong--Seitz I (6E)(b); II pp.218--220, particularly the whole-actor
relabeling preceding (9.27).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.SourceFieldApplication
variable {F K₀ : Type*} [Field F] [Finite F] [CharP F 2] [Field K₀] [Finite K₀]
  {n : ℕ} {hn : 0 < n}

/-- The q-power Frobenius on the field of the original cubic rank-one actor. -/
def sourceFrobenius (F : Type*) [Field F] [Finite F] [CharP F 2] (n : ℕ) : F ≃+* F :=
  iterateFrobeniusEquiv F 2 n

/-- The extension marking intertwines this actual q-Frobenius. -/
def marking (hcard : Nat.card F = (2^n)^3) :
    ScalarMarking (binaryParameters n hn) (sourceFrobenius F n) :=
  scalarMarking hcard (fun _ => rfl)

/-- The independently supplied small rank-one field is identified with the
actual fixed subfield before relabeling its entire rank-one actor. -/
def fixedEquiv (hcard : Nat.card F = (2^n)^3) (hsmall : Nat.card K₀ = 2^n) :
    K₀ ≃+* ScalarMarking.SourceFixed (σ := sourceFrobenius F n) := by
  letI := Fintype.ofFinite K₀
  letI := Fintype.ofFinite (ScalarMarking.SourceFixed (σ := sourceFrobenius F n))
  apply FiniteField.ringEquivOfCardEq
  simpa only [← Nat.card_eq_fintype_card] using
    hsmall.trans (scalarMarking_sourceFixed_card (marking (hn := hn) hcard)).symm

/-- The final fixed-field marking is the restriction of the same extension marking. -/
theorem marking_fixed_coe (hcard : Nat.card F = (2^n)^3)
    (a : ScalarMarking.SourceFixed (σ := sourceFrobenius F n)) :
    ((marking (hn := hn) hcard).fixed a : ExtensionField (binaryParameters n hn)) =
      (marking (hn := hn) hcard).extension a.val := rfl

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (indices : Fin 2 ≃ Fin 2)
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃* PSL(2,K₀))
  (hm : rotationOrder Q = 6) (row : StructuralRow Q split (indices 0) (indices 1))
  (hcard : Nat.card F = (2^n)^3) (hsmall : Nat.card K₀ = 2^n)

/-- Transport the whole original small-field local marking, not a single root. -/
def fixedLocalMarking : localGroup Q split (indices 1) ≃*
    PSL(2,ScalarMarking.SourceFixed (σ := sourceFrobenius F n)) :=
  μj.trans (Atlas.fieldEquivPSL 2 (fixedEquiv (hn := hn) hcard hsmall))

/-- Full source reconstruction from the two actual local field models and
6E(b) structure. The cubic field, its q-Frobenius, the actual fixed field,
compatible scalar markings, root relations and all signed torus laws are
constructed here; only the original ambient normal-generation premise is used. -/
def rootData (hgen : split.unipotentClosure = ⊤) :
    TrialityPresentation.RootData Q split n hn (sourceFrobenius F n) (indices 0) :=
  FullApplication.rootData Q split (sourceFrobenius F n) indices hVi hVj μi
    (fixedLocalMarking (hn := hn) Q split indices μj hcard hsmall) hm row (marking hcard) hgen

section Marked
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (marking₀ : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam) (h : HypothesisF11 L S)

/-- The original F.1.1 data discharge normal generation as well. -/
def markedRootData : TrialityPresentation.RootData Q split n hn (sourceFrobenius F n) (indices 0) :=
  rootData Q split indices hVi hVj μi μj hm row hcard hsmall
    (A2Source.unipotent_normalClosure_eq_top Q marking₀ h split)

include Q split indices hVi hVj μi μj hm row hcard hsmall marking₀ h hn in
/-- The actual final consumer has no assumed scalar marking, module equation,
torus relation, generation certificate or model comparison. -/
theorem concreteComparison : Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) :=
  (markedRootData (hn := hn) Q split indices hVi hVj μi μj hm row hcard hsmall marking₀ h).concreteComparison marking₀
end Marked
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.SourceFieldApplication
