module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanWeights
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.OrthogonalApplication

/-!
# Marked G₂ comparison from the remaining common-field actions

CartanWeights now derives all six torus weights, both Cartan--Weyl equations
and the general braid from the constructed source pinnings. The only new
module inputs below are the short torus's inverse-cube action on E and the
long torus's inverse action on F. Together with the still-explicit lower
positive construction, these supply the full published presentation on
the SAME marked quotient, including F₂ and F₄ and either orientation.

The existing presentation owner provides the model comparison; its one
ambient equivalence preserves U, the full Borel, both endpoints, the full
overlap and the original Sylow. The original specialization uses Q.q,
and the native orientation also reaches the geometric amalgam.

This is a conditional source application, NOT the 6E(a) -> 9A theorem.
The coupled modules must still establish both cross actions with compatible
field labels and construct PartialPositiveData. Earlier source local/kernel
and normal-generation inputs remain explicit. There is no simplicity or
universal-to-original descent assumption.

Source: Fong--Seitz II §7 and (9.9)--(9.21), printed pp.192,213--217;
DGS Theorem D, printed p.224, for the final marked application.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.WeightSource
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
  (hshort : ∀ (a : Fˣ) (b : F),
    alignedTorusHom Q split short (hK short) (μ short) (n short) a *
      (alignedSourceRoots Q split hK μ n short).x 4 b *
      (alignedTorusHom Q split short (hK short) (μ short) (n short) a)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 4 ((a : F)⁻¹^3*b))
  (hlong : ∀ (a : Fˣ) (b : F),
    alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a *
      (alignedSourceRoots Q split hK μ n short).x 5 b *
      (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 5 ((a : F)⁻¹*b))
  (hgen : split.unipotentClosure = ⊤)

/-- Construct every presentation clause from the pinnings and the explicitly
remaining module equations; no BorelWeylData.Relations is assumed. -/
def rootData : RootData Q split F short where
  data := sourceBorelWeyl Q split hK μ n short split.abelian
  relations := by
    obtain ⟨hE,hF⟩ := sourceBorelWeyl_simple_weights_of_cross_actions
      Q split hK μ n short split.abelian hshort hlong
    exact sourceBorelWeyl_relations_of_simple_weights
      Q split hK μ n short split.abelian hm d₀ hE hF
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
    (rootData Q split hm hK μ n short d₀ hshort hlong hgen)

/-- The same equivalence identifies the full B and both parabolics. -/
theorem subgroup_images :
    let f := G2Presentation.quotientEquiv Q split
      (rootData Q split hm hK μ n short d₀ hshort hlong hgen)
    split.U.map f.toMonoidHom = Atlas.G2.unipotent ∧
    Q.tits.B.map f.toMonoidHom = Atlas.G2.borel ∧
    (Q.tits.standardParabolic {Q.simple short}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₁ ∧
    (Q.tits.standardParabolic {Q.simple (1-short)}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₂ :=
  G2Presentation.subgroup_images Q split
    (rootData Q split hm hK μ n short d₀ hshort hlong hgen)

theorem comparison_left (a : parabolic L S 0) :
    ((comparison Q split e hm hK μ n short d₀ hshort hlong hgen).left a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hshort hlong hgen)
        (MarkedLocal.endpointMap Q e 0 a) := rfl

theorem comparison_right (a : parabolic L S 1) :
    ((comparison Q split e hm hK μ n short d₀ hshort hlong hgen).right a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hshort hlong hgen)
        (MarkedLocal.endpointMap Q e 1 a) := rfl

/-- Both squares use the entire original overlap. -/
theorem comparison_squares (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := comparison Q split e hm hK μ n short d₀ hshort hlong hgen
    c.left ⟨b,b.property.1⟩ = (flagAmalgam F short).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ = (flagAmalgam F short).right (c.middle b) :=
  ⟨(comparison Q split e hm hK μ n short d₀ hshort hlong hgen).left_commutes b,
    (comparison Q split e hm hK μ n short d₀ hshort hlong hgen).right_commutes b⟩

/-- Original S maps onto the same model U. -/
theorem source_sylow_image (h : HypothesisF11 L S) :
    (MarkedLocal.sylowMap Q e h).range.map
      (G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hshort hlong hgen)).toMonoidHom =
      Atlas.G2.unipotent :=
  G2Presentation.source_sylow_image Q e h split
    (rootData Q split hm hK μ n short d₀ hshort hlong hgen)

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
    (rootData Q split hm hK μ n 0 d₀ hshort hlong hgen)

theorem geometric_squares (hshortIndex : short = 0)
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := geometricComparison Q split e hm hK μ n short d₀ hshort hlong hgen hshortIndex
    c.left ⟨b,b.property.1⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).right (c.middle b) :=
  ⟨(geometricComparison Q split e hm hK μ n short d₀ hshort hlong hgen hshortIndex).left_commutes b,
    (geometricComparison Q split e hm hK μ n short d₀ hshort hlong hgen hshortIndex).right_commutes b⟩

section Original
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (d₀ : PartialPositiveData (alignedSourceRoots Q split hK μ n short))
  (hshort : ∀ (a : Fˣ) (b : F),
    alignedTorusHom Q split short (hK short) (μ short) (n short) a *
      (alignedSourceRoots Q split hK μ n short).x 4 b *
      (alignedTorusHom Q split short (hK short) (μ short) (n short) a)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 4 ((a : F)⁻¹^3*b))
  (hlong : ∀ (a : Fˣ) (b : F),
    alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a *
      (alignedSourceRoots Q split hK μ n short).x 5 b *
      (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 5 ((a : F)⁻¹*b))
  (hgen : split.unipotentClosure = ⊤)


/-- The original left endpoint uses its literal Q.q representative. -/
theorem original_left (a : parabolic L S 0) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short d₀ hshort hlong hgen).left a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hshort hlong hgen)
        (Q.q ⟨a,parabolic_le_generated 0 a.property⟩) :=
  G2Presentation.originalComparison_left_apply Q split
    (rootData Q split hm hK μ n short d₀ hshort hlong hgen) a

/-- The original right endpoint uses its literal Q.q representative. -/
theorem original_right (a : parabolic L S 1) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short d₀ hshort hlong hgen).right a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hshort hlong hgen)
        (Q.q ⟨a,parabolic_le_generated 1 a.property⟩) :=
  G2Presentation.originalComparison_right_apply Q split
    (rootData Q split hm hK μ n short d₀ hshort hlong hgen) a

/-- The whole overlap uses the same quotient map as both endpoints. -/
theorem original_middle (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short d₀ hshort hlong hgen).middle b :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short d₀ hshort hlong hgen)
        (Q.q ⟨b,parabolic_le_generated 0 b.property.1⟩) :=
  G2Presentation.originalComparison_middle_apply Q split
    (rootData Q split hm hK μ n short d₀ hshort hlong hgen) b
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.WeightSource
