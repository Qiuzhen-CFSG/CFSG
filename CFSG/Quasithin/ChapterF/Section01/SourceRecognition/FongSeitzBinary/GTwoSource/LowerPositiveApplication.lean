module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.LowerPositive
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.ForcedCartanApplication

/-!
# The lower source equations in the full marked G₂ consumer

Relative normality of the two actual radicals proves five adjacent-root
commutations. Weyl transport reduces the five other commutations to the
literal subgroup clauses BA = 1 and EC = 1, respectively (9.2) and (9.5).
The long reflection also derives FC from DC. Together these results remove
eight independent commutation premises and the FC equation from the existing
lower positive input, uniformly over F₂, F₄ and larger fields.

Feed the resulting PartialPositiveData directly to the already proved
ForcedCartanSource construction. All full-Borel, both-endpoint, original Q.q,
original S and geometric comparisons use those same constructed data and
retain both orientations. No model-presentation proof is repeated.

The two displayed source commutator clauses and LowerPositiveData remain
obligations of the 6E(a) -> 9A proof. In particular, this module does not
construct the coupled natural/tensor modules, their compatible field markings,
the auxiliary torus, or the binary mixed equations, and does not claim
completion of source recognition. Earlier row selection and normal generation
remain with the existing source assembly.

Source: Fong--Seitz I (3G), pp.14--16, (5C), pp.25--26;
II (9.2), (9.5), (9.13)--(9.21), pp.211--217; DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.LowerPositiveSource
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
  (hba : ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥)
  (hec : ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥)
  (d₀ : LowerPositiveData (alignedSourceRoots Q split hK μ n short))
  (hgen : split.unipotentClosure = ⊤)

/-- All discarded positive premises are proved before applying the existing
full source constructor. The two source clauses and mixed data are retained. -/
def rootData : RootData Q split F short :=
  ForcedCartanSource.rootData Q split hm hK μ n short
    (aligned_partial_of_lower Q split hK μ n short hm hba hec d₀) hgen

/-- Apply the existing full comparison with either orientation. -/
def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F short) :=
  G2Presentation.comparison Q e split
    (rootData Q split hm hK μ n short hba hec d₀ hgen)

/-- The same equivalence identifies the full B and both parabolics. -/
theorem subgroup_images :
    let f := G2Presentation.quotientEquiv Q split
      (rootData Q split hm hK μ n short hba hec d₀ hgen)
    split.U.map f.toMonoidHom = Atlas.G2.unipotent ∧
    Q.tits.B.map f.toMonoidHom = Atlas.G2.borel ∧
    (Q.tits.standardParabolic {Q.simple short}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₁ ∧
    (Q.tits.standardParabolic {Q.simple (1-short)}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₂ :=
  G2Presentation.subgroup_images Q split
    (rootData Q split hm hK μ n short hba hec d₀ hgen)

theorem comparison_left (a : parabolic L S 0) :
    ((comparison Q split e hm hK μ n short hba hec d₀ hgen).left a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hba hec d₀ hgen)
        (MarkedLocal.endpointMap Q e 0 a) := rfl

theorem comparison_right (a : parabolic L S 1) :
    ((comparison Q split e hm hK μ n short hba hec d₀ hgen).right a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hba hec d₀ hgen)
        (MarkedLocal.endpointMap Q e 1 a) := rfl

/-- Both squares use the entire original overlap. -/
theorem comparison_squares (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := comparison Q split e hm hK μ n short hba hec d₀ hgen
    c.left ⟨b,b.property.1⟩ = (flagAmalgam F short).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ = (flagAmalgam F short).right (c.middle b) :=
  ⟨(comparison Q split e hm hK μ n short hba hec d₀ hgen).left_commutes b,
    (comparison Q split e hm hK μ n short hba hec d₀ hgen).right_commutes b⟩

/-- Original S maps onto the same model U. -/
theorem source_sylow_image (h : HypothesisF11 L S) :
    (MarkedLocal.sylowMap Q e h).range.map
      (G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hba hec d₀ hgen)).toMonoidHom =
      Atlas.G2.unipotent :=
  G2Presentation.source_sylow_image Q e h split
    (rootData Q split hm hK μ n short hba hec d₀ hgen)

include hm hba hec d₀ in
/-- The same roots retain the published positive map and both original endpoints. -/
theorem positive_marked_application (h : HypothesisF11 L S) :
    ∃ f : Atlas.G2.unipotent (K := F) →* S, Function.Surjective f ∧
      ∀ (i : Fin 2) (a : Fin 6 → F),
        let s := f (Atlas.G2.unipotentEquiv a)
        MarkedLocal.endpointMap Q e i
          ⟨s,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
            (alignedSourceRoots Q split hK μ n short).product a :=
  ForcedCartanSource.positive_marked_application Q split e hm hK μ n short
    (aligned_partial_of_lower Q split hK μ n short hm hba hec d₀) h

/-- The native first-short orientation reaches the actual geometric model. -/
def geometricComparison (hshortIndex : short = 0) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)) := by
  subst short
  exact G2Presentation.geometricComparison Q e split
    (rootData Q split hm hK μ n 0 hba hec d₀ hgen)

theorem geometric_squares (hshortIndex : short = 0)
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := geometricComparison Q split e hm hK μ n short hba hec d₀ hgen hshortIndex
    c.left ⟨b,b.property.1⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).right (c.middle b) :=
  ⟨(geometricComparison Q split e hm hK μ n short hba hec d₀ hgen hshortIndex).left_commutes b,
    (geometricComparison Q split e hm hK μ n short hba hec d₀ hgen hshortIndex).right_commutes b⟩

section Original
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hba : ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥)
  (hec : ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥)
  (d₀ : LowerPositiveData (alignedSourceRoots Q split hK μ n short))
  (hgen : split.unipotentClosure = ⊤)


/-- The original left endpoint uses its literal Q.q representative. -/
theorem original_left (a : parabolic L S 0) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short hba hec d₀ hgen).left a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hba hec d₀ hgen)
        (Q.q ⟨a,parabolic_le_generated 0 a.property⟩) :=
  G2Presentation.originalComparison_left_apply Q split
    (rootData Q split hm hK μ n short hba hec d₀ hgen) a

/-- The original right endpoint uses its literal Q.q representative. -/
theorem original_right (a : parabolic L S 1) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short hba hec d₀ hgen).right a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hba hec d₀ hgen)
        (Q.q ⟨a,parabolic_le_generated 1 a.property⟩) :=
  G2Presentation.originalComparison_right_apply Q split
    (rootData Q split hm hK μ n short hba hec d₀ hgen) a

/-- The whole overlap uses the same quotient map as both endpoints. -/
theorem original_middle (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n short hba hec d₀ hgen).middle b :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n short hba hec d₀ hgen)
        (Q.q ⟨b,parabolic_le_generated 0 b.property.1⟩) :=
  G2Presentation.originalComparison_middle_apply Q split
    (rootData Q split hm hK μ n short hba hec d₀ hgen) b
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.LowerPositiveSource
