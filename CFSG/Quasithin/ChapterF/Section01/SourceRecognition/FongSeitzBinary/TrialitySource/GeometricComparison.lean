module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.LocalModelData

/-!
# Full triality comparison for an independently marked geometric quotient

The earlier geometric construction supplies its actual isomorphism to
Q.standardAmalgam. Construct all source field, positive and signed root,
torus and Weyl data on that same Q from the earlier local models and
structural row. One ambient equivalence then supplies the complete Borel
map, both endpoint maps and both inclusion squares. Original source F.1.1
is transported through the supplied marking solely to prove normal generation.

The numerator X is arbitrary and may be the infinite universal completion.
There is no universal-to-original-group descent premise. This is the accepted
carrier-general geometric boundary: the separately owned apartment-exchange
construction supplies e₀, rather than being expanded inside every dependent
local permutation-group type. Every positive binary exponent and both
orientations are retained.

Source: DGS Theorem D and its apartment-exchange quotient; Fong--Seitz I
(6E)(b), II §9B. The full comparison is the existing checked presentation.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricComparison
variable {X F K₀ : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  [Field K₀] [Finite K₀] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (indices : Fin 2 ≃ Fin 2)
  {n : ℕ} {hn : 0 < n} (d : LocalModelData (F := F) (K₀ := K₀) Q split indices n)
  {A C E : Type*} [Group A] [Group C] [Group E] {α : RankTwoAmalgam A C E}
  (e₀ : RankTwoAmalgam.Iso α Q.standardAmalgam)
  {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (eα : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) α)
  (h : HypothesisF11 L S)

/-- The entire reconstructed source presentation, on the same marked geometric quotient. -/
def rootData : TrialityPresentation.RootData Q split n hn
    (SourceFieldApplication.sourceFrobenius F n) (indices 0) :=
  d.markedRootData (eα.trans e₀) h

local notation "r" => rootData (hn := hn) Q split indices d e₀ eα h

/-- Compose the actual earlier geometric marking with the fully proved triality marking. -/
def comparison : RankTwoAmalgam.Iso α (TrialityPresentation.flagAmalgam n hn (indices 0)) :=
  (r).comparison e₀

@[simp] theorem comparison_left_apply (a : A) :
    ((comparison (hn := hn) Q split indices d e₀ eα h).left a : BinaryCarrier n hn) =
      (r).bruhat.quotientEquiv (e₀.left a : X ⧸ Q.D) := rfl

@[simp] theorem comparison_middle_apply (a : C) :
    ((comparison (hn := hn) Q split indices d e₀ eα h).middle a : BinaryCarrier n hn) =
      (r).bruhat.quotientEquiv (e₀.middle a : X ⧸ Q.D) := rfl

@[simp] theorem comparison_right_apply (a : E) :
    ((comparison (hn := hn) Q split indices d e₀ eα h).right a : BinaryCarrier n hn) =
      (r).bruhat.quotientEquiv (e₀.right a : X ⧸ Q.D) := rfl

/-- Both endpoint squares use the full original geometric overlap. -/
theorem endpoint_squares (a : C) :
    let c := comparison (hn := hn) Q split indices d e₀ eα h
    c.left (α.left a) = (TrialityPresentation.flagAmalgam n hn (indices 0)).left (c.middle a) ∧
    c.right (α.right a) = (TrialityPresentation.flagAmalgam n hn (indices 0)).right (c.middle a) :=
  ⟨(comparison (hn := hn) Q split indices d e₀ eα h).left_commutes a,
    (comparison (hn := hn) Q split indices d e₀ eα h).right_commutes a⟩

/-- The middle map covers the entire source Borel. -/
theorem full_borel : Q.tits.B.map (r).bruhat.quotientEquiv.toMonoidHom =
    Parabolics.borel (binaryParameters n hn) := (r).bruhat.quotientEquiv_borel

/-- The original Sylow image is retained under the same Q.q and geometric marking. -/
theorem nativeHom_range_marked : (r).positive.nativeHom.range =
    (MarkedLocal.sylowMap Q (eα.trans e₀) h).range :=
  (r).positive.nativeHom_range_marked (eα.trans e₀) h

include Q split indices d e₀ eα h hn in
/-- Apply the existing full marked-presentation consumer to the reconstructed data. -/
theorem concreteComparison : Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison α :=
  (r).concreteComparison e₀
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricComparison
