module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkingAlignment

/-!
# Full marked A₂ recognition from independent source geometry

The independently transported original natural cores give one projective
field chart and six compatible generating roots on the SAME finite
quotient. Sylow alignment supplies the actual U and both negative-root
placements, and the accepted presentation comparison then identifies the
whole Borel and both full endpoints in either orientation.

Every relation and generation clause is proved internally. No RootData,
model equivalence, unknown-group simplicity or perfect-local-factor premise
is supplied; fields of orders two and four are included. The full local
marking need not extend to the original ambient completion. Earlier natural
actions, source centerfreeness and the m=3 parameter remain the genuine
Chapter 6--10 and apartment-producer inputs, discharged by source assembly.
Source: DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224; AS F.1.1--3.
-/

@[expose] public noncomputable section
open Subgroup Configuration Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace MarkedRecognition
variable {G X : Type*} [Group G] [Group X] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    d.standardAmalgam)
  (h : HypothesisF11 L S)

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance markedRecognitionFieldAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
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

include mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter in
/-- The source geometry produces every accepted A₂ root-data clause, including
full generation, the actual U, and both negative-root placements. -/
theorem exists_rootData : ∃ i : Fin 2, Nonempty (RootData d split k₁ i) := by
  let := MarkedPlane.plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
  obtain ⟨o,ho⟩ := Configuration.Nondegenerate.exists_point
    (P := Point (TriangleGeometry.family d)) (QuotientPlane.axis d)
  exact MarkingAlignment.exists_rootData d split
    (MarkedProjectiveCoordinates.unmarkedEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter ⟨o,ho⟩)

/-- The actual source orientation selected by the two distinct full endpoints. -/
def pointIndex : Fin 2 := (exists_rootData d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).choose

/-- Six simultaneous roots on the same quotient, with all source markings proved. -/
def rootData : RootData d split k₁ (pointIndex d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split) :=
  Classical.choice (exists_rootData d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).choose_spec

/-- The source recognition equivalence on the whole quotient, including q=2,4. -/
def quotientEquiv : (X ⧸ d.D) ≃* PSL(3,k₁) :=
  LinearThreePresentation.quotientEquiv d mark h split
    (rootData d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)

/-- The source root parameters are retained over the one original natural field. -/
theorem quotientEquiv_root (r : Root 3) (a : k₁) :
    quotientEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split
      ((rootData d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).x r a) = projectiveRoot r a :=
  LinearThreePresentation.quotientEquiv_root d mark h split _ r a

/-- Apply the accepted presentation consumer to the original full inclusion amalgam. -/
def comparison : Theory.GroupTheory.RankTwoAmalgam.Iso
    (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam k₁ (pointIndex d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)) :=
  LinearThreePresentation.comparison d mark h split
    (rootData d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)

/-- Literal original left endpoint, with its unchanged endpoint marking. -/
theorem comparison_left_apply (a : parabolic L S 0) :
    ((comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).left a : PSL(3,k₁)) =
      quotientEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split
        (mark.left a : X ⧸ d.D) :=
  LinearThreePresentation.comparison_left_apply d mark h split _ a

/-- The entire common Borel uses that same full-overlap marking. -/
theorem comparison_middle_apply (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).middle b : PSL(3,k₁)) =
      quotientEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split
        (mark.middle b : X ⧸ d.D) :=
  LinearThreePresentation.comparison_middle_apply d mark h split _ b

/-- Literal original right endpoint, in the same orientation and over the same field. -/
theorem comparison_right_apply (a : parabolic L S 1) :
    ((comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).right a : PSL(3,k₁)) =
      quotientEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split
        (mark.right a : X ⧸ d.D) :=
  LinearThreePresentation.comparison_right_apply d mark h split _ a

/-- Both full-overlap inclusion squares commute under the constructed recognition. -/
theorem comparison_squares (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).left ⟨b,b.property.1⟩ =
      (flagAmalgam k₁ (pointIndex d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)).left
        ((comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).middle b) ∧
    (comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).right ⟨b,b.property.2⟩ =
      (flagAmalgam k₁ (pointIndex d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)).right
        ((comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).middle b) :=
  ⟨(comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).left_commutes b,
    (comparison d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).right_commutes b⟩

/-- The whole original common Sylow has exactly the model upper-unitriangular image. -/
theorem source_sylow_image :
    (MarkedLocal.sylowMap d mark h).range.map
      (quotientEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).toMonoidHom =
        Matrix.PSL3.LinearThree.unipotent k₁ :=
  LinearThreePresentation.source_sylow_image d mark h split _

/-- All full marked subgroup images, in the selected orientation. -/
theorem subgroup_images :
    split.U.map (quotientEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).toMonoidHom =
      Matrix.PSL3.LinearThree.unipotent k₁ ∧
    d.tits.B.map (quotientEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).toMonoidHom =
      Matrix.PSL3.LinearThree.borel k₁ ∧
    (d.tits.standardParabolic {d.simple (pointIndex d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)}).map
      (quotientEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).toMonoidHom =
        Matrix.PSL3.LinearThree.pointParabolic k₁ ∧
    (d.tits.standardParabolic {d.simple (1 - pointIndex d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split)}).map
      (quotientEquiv d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter split).toMonoidHom =
        Matrix.PSL3.LinearThree.lineParabolic k₁ :=
  LinearThreePresentation.subgroup_images d mark h split _

end MarkedRecognition

/-- Replace the source intersection presentation by its proved whole-Borel presentation.
Both endpoint maps are the identity; the entire overlap follows F.1.3(6). -/
def intersectionAmalgamIso {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (commonBorel L S) (parabolic L S 1) (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)) where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (lemma_F_1_3_6 h)
  right := MulEquiv.refl _
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
