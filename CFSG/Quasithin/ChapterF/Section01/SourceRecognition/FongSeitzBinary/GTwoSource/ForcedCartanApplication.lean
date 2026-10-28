module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.ForcedCartanWeights
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.OrthogonalApplication

/-!
# Full marked G₂ comparison without separate Cartan cross actions

The lower positive construction now determines the Cartan cross actions:
ForcedCartanWeights compares the A and C coefficients of the FE equation
under the two actual rank-one tori. This removes both independent action
premises from the full marked comparison, including q=2 and q=4.

The unchanged model presentation supplies the full Borel and both endpoint
identifications. All maps below live on the original marked quotient; the
original specializations retain Q.q, S, and both endpoint representatives,
and the first-short orientation reaches the geometric amalgam.

This remains conditional on PartialPositiveData. Its lower mixed equations,
commutations and auxiliary torus must still be constructed from the genuine
6E(a) coupled-module input. No source-family completion is asserted.

Source: Fong--Seitz II (9.13)--(9.21), pp.215--217; DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.ForcedCartanSource
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (d₀ : PartialPositiveData (alignedSourceRoots Q split hK μ n short))
  (hgen : split.unipotentClosure = ⊤)

/-- Construct every presentation clause from the lower positive input.
Both common-field Cartan cross actions are proved, rather than assumed. -/
def rootData : RootData Q split F short where
  data := sourceBorelWeyl Q split hK μ n short split.abelian
  relations := sourceBorelWeyl_relations_of_partial Q split hK μ n short hm d₀
  generate := sourceBorelWeyl_whole Q split hK μ n short split.abelian hm hgen
  positive := alignedSourceRoots_generated Q split hK μ n short hm
  highest_nontrivial := alignedSourceRoots_highest_nontrivial Q split hK μ n short
  short_placement := (sourceReflection_placements Q split n short).1
  long_placement := (sourceReflection_placements Q split n short).2

/-- Apply the existing full comparison with either orientation. -/
def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F short) :=
  G2Presentation.comparison Q e split
    (rootData Q split hm hK μ n short d₀ hgen)

/-- The same equivalence identifies the full B and both parabolics. -/
theorem subgroup_images :
    let f := G2Presentation.quotientEquiv Q split
      (rootData Q split hm hK μ n short d₀ hgen)
    split.U.map f.toMonoidHom = Atlas.G2.unipotent ∧
    Q.tits.B.map f.toMonoidHom = Atlas.G2.borel ∧
    (Q.tits.standardParabolic {Q.simple short}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₁ ∧
    (Q.tits.standardParabolic {Q.simple (1-short)}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₂ :=
  G2Presentation.subgroup_images Q split
    (rootData Q split hm hK μ n short d₀ hgen)

theorem comparison_left (a : parabolic L S 0) :
    ((comparison Q split e hm hK μ n short d₀ hgen).left a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hgen)
        (MarkedLocal.endpointMap Q e 0 a) := rfl

theorem comparison_right (a : parabolic L S 1) :
    ((comparison Q split e hm hK μ n short d₀ hgen).right a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hgen)
        (MarkedLocal.endpointMap Q e 1 a) := rfl

/-- Both squares use the entire original overlap. -/
theorem comparison_squares (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := comparison Q split e hm hK μ n short d₀ hgen
    c.left ⟨b,b.property.1⟩ = (flagAmalgam F short).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ = (flagAmalgam F short).right (c.middle b) :=
  ⟨(comparison Q split e hm hK μ n short d₀ hgen).left_commutes b,
    (comparison Q split e hm hK μ n short d₀ hgen).right_commutes b⟩

/-- Original S maps onto the same model U. -/
theorem source_sylow_image (h : HypothesisF11 L S) :
    (MarkedLocal.sylowMap Q e h).range.map
      (G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hgen)).toMonoidHom =
      Atlas.G2.unipotent :=
  G2Presentation.source_sylow_image Q e h split
    (rootData Q split hm hK μ n short d₀ hgen)

include hm d₀ in
/-- The same roots retain the published positive map and both original endpoints. -/
theorem positive_marked_application (h : HypothesisF11 L S) :
    ∃ f : Atlas.G2.unipotent (K := F) →* S, Function.Surjective f ∧
      ∀ (i : Fin 2) (a : Fin 6 → F),
        let s := f (Atlas.G2.unipotentEquiv a)
        MarkedLocal.endpointMap Q e i
          ⟨s,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
            (alignedSourceRoots Q split hK μ n short).product a :=
  OrthogonalSource.positive_marked_application Q split e hm hK μ n short d₀ h

/-- The native first-short orientation reaches the actual geometric model. -/
def geometricComparison (hshortIndex : short = 0) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)) := by
  subst short
  exact G2Presentation.geometricComparison Q e split
    (rootData Q split hm hK μ n 0 d₀ hgen)

theorem geometric_squares (hshortIndex : short = 0)
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := geometricComparison Q split e hm hK μ n short d₀ hgen hshortIndex
    c.left ⟨b,b.property.1⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).right (c.middle b) :=
  ⟨(geometricComparison Q split e hm hK μ n short d₀ hgen hshortIndex).left_commutes b,
    (geometricComparison Q split e hm hK μ n short d₀ hgen hshortIndex).right_commutes b⟩

section Original
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (d₀ : PartialPositiveData (alignedSourceRoots Q split hK μ n short))
  (hgen : split.unipotentClosure = ⊤)


/-- The original left endpoint uses its literal Q.q representative. -/
theorem original_left (a : parabolic L S 0) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short d₀ hgen).left a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hgen)
        (Q.q ⟨a,parabolic_le_generated 0 a.property⟩) :=
  G2Presentation.originalComparison_left_apply Q split
    (rootData Q split hm hK μ n short d₀ hgen) a

/-- The original right endpoint uses its literal Q.q representative. -/
theorem original_right (a : parabolic L S 1) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short d₀ hgen).right a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hgen)
        (Q.q ⟨a,parabolic_le_generated 1 a.property⟩) :=
  G2Presentation.originalComparison_right_apply Q split
    (rootData Q split hm hK μ n short d₀ hgen) a

/-- The whole overlap uses the same quotient map as both endpoints. -/
theorem original_middle (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short d₀ hgen).middle b :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hgen)
        (Q.q ⟨b,parabolic_le_generated 0 b.property.1⟩) :=
  G2Presentation.originalComparison_middle_apply Q split
    (rootData Q split hm hK μ n short d₀ hgen) b
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.ForcedCartanSource
