module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.RootGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkingAlignment

/-!
# Marked A₂ recognition on the literal original source quotient

The actual centerfree natural cores and m=3 geometry construct one projective
field chart, all six compatible roots, every elementary relation and full
root generation. Sylow alignment then supplies positive closure equal to
the original U and both actual negative-root placements. Applying the proved
presentation comparison gives both full endpoint maps and the whole Borel
map through the unchanged source quotient, in either orientation.

No RootData, model equivalence, simplicity or perfect-local-factor premise
is supplied here; q=2 and q=4 are included. The input SourceQuotient is a
quotient of the literal generated source carrier. The independent
marked-quotient version is constructed in MarkedRecognition; neither
application asserts a universal-to-ambient descent.

Source: DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224; AS F.1.1--3.
-/

@[expose] public noncomputable section
open Subgroup Configuration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace Recognition
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (d : SourceQuotient L S)
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance recognitionFieldAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)
  (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set (generated L S)))
  (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set (generated L S)))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
  (hm : RootCoordinates.rotationOrder d = 3) (hcenter : centerIn c₁.actor = ⊥)

variable (split : SplitData d.tits)
open Matrix.PSL3.RootPresentationRecognition
open Theory.SpecificGroups.LinearHigher

include h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter in
/-- The source geometry produces every accepted A₂ root-data clause, including
full generation, the actual U, and both negative-root placements. -/
theorem exists_rootData : ∃ i : Fin 2, Nonempty (RootData d split k₁ i) := by
  let := OriginalCoordinates.plane h d c₀ c₁ hn₀ hn₁ E₀ hm
  obtain ⟨o,ho⟩ := Configuration.Nondegenerate.exists_point
    (P := Point (TriangleGeometry.family d)) (QuotientPlane.axis d)
  exact MarkingAlignment.exists_rootData d split
    (ProjectiveCoordinates.unmarkedEquiv h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter ⟨o,ho⟩ split)

/-- The actual source orientation selected by the two distinct full endpoints. -/
def pointIndex : Fin 2 := (exists_rootData h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).choose

/-- Six simultaneous roots on the same quotient, with all source markings proved. -/
def rootData : RootData d split k₁ (pointIndex h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split) :=
  Classical.choice (exists_rootData h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).choose_spec

/-- The source recognition equivalence on the whole quotient, including q=2,4. -/
def quotientEquiv : ((generated L S) ⧸ d.D) ≃* PSL(3,k₁) :=
  LinearThreePresentation.quotientEquiv d (originalMarkedIso d) h split
    (rootData h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)

/-- The source root parameters are retained over the one original natural field. -/
theorem quotientEquiv_root (r : Root 3) (a : k₁) :
    quotientEquiv h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split
      ((rootData h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).x r a) = projectiveRoot r a :=
  LinearThreePresentation.quotientEquiv_root d (originalMarkedIso d) h split _ r a

/-- Apply the accepted presentation consumer to the original full inclusion amalgam. -/
def comparison : Theory.GroupTheory.RankTwoAmalgam.Iso
    (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam k₁ (pointIndex h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)) :=
  LinearThreePresentation.originalComparison h d split
    (rootData h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)

/-- Literal original left endpoint, with its unchanged quotient representative. -/
theorem comparison_left_apply (a : parabolic L S 0) :
    ((comparison h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).left a : PSL(3,k₁)) =
      quotientEquiv h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split
        (d.q ⟨a,parabolic_le_generated 0 a.property⟩) :=
  LinearThreePresentation.originalComparison_left_apply h d split _ a

/-- The entire common Borel uses that same literal original projection. -/
theorem comparison_middle_apply (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).middle b : PSL(3,k₁)) =
      quotientEquiv h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split
        (d.q ⟨b,parabolic_le_generated 0 b.property.1⟩) :=
  LinearThreePresentation.originalComparison_middle_apply h d split _ b

/-- Literal original right endpoint, in the same orientation and over the same field. -/
theorem comparison_right_apply (a : parabolic L S 1) :
    ((comparison h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).right a : PSL(3,k₁)) =
      quotientEquiv h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split
        (d.q ⟨a,parabolic_le_generated 1 a.property⟩) :=
  LinearThreePresentation.originalComparison_right_apply h d split _ a

/-- Both full-overlap inclusion squares commute under the constructed recognition. -/
theorem comparison_squares (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).left ⟨b,b.property.1⟩ =
      (flagAmalgam k₁ (pointIndex h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)).left
        ((comparison h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).middle b) ∧
    (comparison h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).right ⟨b,b.property.2⟩ =
      (flagAmalgam k₁ (pointIndex h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)).right
        ((comparison h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).middle b) :=
  ⟨(comparison h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).left_commutes b,
    (comparison h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).right_commutes b⟩

/-- The whole original common Sylow has exactly the model upper-unitriangular image. -/
theorem source_sylow_image :
    (MarkedLocal.sylowMap d (originalMarkedIso d) h).range.map
      (quotientEquiv h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).toMonoidHom =
        Matrix.PSL3.LinearThree.unipotent k₁ :=
  LinearThreePresentation.source_sylow_image d (originalMarkedIso d) h split _

end Recognition
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
