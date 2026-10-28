module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.ShortRootModule
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.G2Presentation.Recognition

/-!
# The marked G₂ comparison from the source DC pairing

The short-root radical calculation now derives FD and the entire FE
formula from normalized DC alone. Together with the previously proved EB,
commutations and Cartan actions, it constructs all Borel--Weyl equations.
Apply the published presentation directly to these actual source maps.
The same comparison preserves U, the full Borel, both oriented parabolics,
original S, literal Q.q representatives and the entire overlap. The positive
and geometric applications are retained, including q=2 and q=4.

The sole remaining mixed-equation premise is normalized DC on these same
pinnings. Constructing the compatible whole-pinning labels and that pairing
from genuine 6E(a) radical data is still required. The earlier structural,
row-selection and whole-generation premises remain with their source
assembly owners; this is not completion of 6E(a) -> 9A.

Source: Fong--Seitz II (9.4), (9.13)--(9.21), pp.212,215--217;
DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.ShortModuleSource
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
  (hdc : ∀ d c : F, (alignedSourceRoots Q split hK μ n short).x 3 d *
    (alignedSourceRoots Q split hK μ n short).x 2 c =
      (alignedSourceRoots Q split hK μ n short).x 0 (c*d) *
        (alignedSourceRoots Q split hK μ n short).x 2 c *
          (alignedSourceRoots Q split hK μ n short).x 3 d)
  (hgen : split.unipotentClosure = ⊤)

/-- Construct all equations, generation and placements from the source pinnings
and normalized DC, retaining the independent whole-generation premise. -/
def rootData : RootData Q split F short where
  data := sourceBorelWeyl Q split hK μ n short split.abelian
  relations := sourceBorelWeyl_relations_of_dc Q split hK μ n short hm hdc
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
    (rootData Q split hm hK μ n short hdc hgen)

/-- The same equivalence identifies the full B and both parabolics. -/
theorem subgroup_images :
    let f := G2Presentation.quotientEquiv Q split
      (rootData Q split hm hK μ n short hdc hgen)
    split.U.map f.toMonoidHom = Atlas.G2.unipotent ∧
    Q.tits.B.map f.toMonoidHom = Atlas.G2.borel ∧
    (Q.tits.standardParabolic {Q.simple short}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₁ ∧
    (Q.tits.standardParabolic {Q.simple (1-short)}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₂ :=
  G2Presentation.subgroup_images Q split
    (rootData Q split hm hK μ n short hdc hgen)

theorem comparison_left (a : parabolic L S 0) :
    ((comparison Q split e hm hK μ n short hdc hgen).left a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hdc hgen)
        (MarkedLocal.endpointMap Q e 0 a) := rfl

theorem comparison_right (a : parabolic L S 1) :
    ((comparison Q split e hm hK μ n short hdc hgen).right a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hdc hgen)
        (MarkedLocal.endpointMap Q e 1 a) := rfl

/-- Both squares use the entire original overlap. -/
theorem comparison_squares (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := comparison Q split e hm hK μ n short hdc hgen
    c.left ⟨b,b.property.1⟩ = (flagAmalgam F short).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ = (flagAmalgam F short).right (c.middle b) :=
  ⟨(comparison Q split e hm hK μ n short hdc hgen).left_commutes b,
    (comparison Q split e hm hK μ n short hdc hgen).right_commutes b⟩

/-- Original S maps onto the same model U. -/
theorem source_sylow_image (h : HypothesisF11 L S) :
    (MarkedLocal.sylowMap Q e h).range.map
      (G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hdc hgen)).toMonoidHom =
      Atlas.G2.unipotent :=
  G2Presentation.source_sylow_image Q e h split
    (rootData Q split hm hK μ n short hdc hgen)

include hm hdc in
/-- The same roots retain the published positive map and both original endpoints. -/
theorem positive_marked_application (h : HypothesisF11 L S) :
    ∃ f : Atlas.G2.unipotent (K := F) →* S, Function.Surjective f ∧
      ∀ (i : Fin 2) (a : Fin 6 → F),
        let s := f (Atlas.G2.unipotentEquiv a)
        MarkedLocal.endpointMap Q e i
          ⟨s,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
            (alignedSourceRoots Q split hK μ n short).product a :=
by
  let roots := alignedSourceRoots Q split hK μ n short
  let rels := aligned_positive_relations_of_dc Q split hK μ n short hm hdc
  have hU := alignedSourceRoots_generated Q split hK μ n short hm
  refine ⟨G2Presentation.sourceSylowHom Q split roots rels hU e h,
    G2Presentation.sourceSylowHom_surjective Q split roots rels hU e h, ?_⟩
  intro i a
  exact G2Presentation.sourceSylowHom_endpoint Q split roots rels hU e h i a

/-- The native first-short orientation reaches the actual geometric model. -/
def geometricComparison (hshortIndex : short = 0) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)) := by
  subst short
  exact G2Presentation.geometricComparison Q e split
    (rootData Q split hm hK μ n 0 hdc hgen)

theorem geometric_squares (hshortIndex : short = 0)
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := geometricComparison Q split e hm hK μ n short hdc hgen hshortIndex
    c.left ⟨b,b.property.1⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).right (c.middle b) :=
  ⟨(geometricComparison Q split e hm hK μ n short hdc hgen hshortIndex).left_commutes b,
    (geometricComparison Q split e hm hK μ n short hdc hgen hshortIndex).right_commutes b⟩

section Original
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hdc : ∀ d c : F, (alignedSourceRoots Q split hK μ n short).x 3 d *
    (alignedSourceRoots Q split hK μ n short).x 2 c =
      (alignedSourceRoots Q split hK μ n short).x 0 (c*d) *
        (alignedSourceRoots Q split hK μ n short).x 2 c *
          (alignedSourceRoots Q split hK μ n short).x 3 d)
  (hgen : split.unipotentClosure = ⊤)


/-- The original left endpoint uses its literal Q.q representative. -/
theorem original_left (a : parabolic L S 0) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short hdc hgen).left a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hdc hgen)
        (Q.q ⟨a,parabolic_le_generated 0 a.property⟩) :=
  G2Presentation.originalComparison_left_apply Q split
    (rootData Q split hm hK μ n short hdc hgen) a

/-- The original right endpoint uses its literal Q.q representative. -/
theorem original_right (a : parabolic L S 1) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short hdc hgen).right a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hdc hgen)
        (Q.q ⟨a,parabolic_le_generated 1 a.property⟩) :=
  G2Presentation.originalComparison_right_apply Q split
    (rootData Q split hm hK μ n short hdc hgen) a

/-- The whole overlap uses the same quotient map as both endpoints. -/
theorem original_middle (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short hdc hgen).middle b :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hdc hgen)
        (Q.q ⟨b,parabolic_le_generated 0 b.property.1⟩) :=
  G2Presentation.originalComparison_middle_apply Q split
    (rootData Q split hm hK μ n short hdc hgen) b
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.ShortModuleSource
