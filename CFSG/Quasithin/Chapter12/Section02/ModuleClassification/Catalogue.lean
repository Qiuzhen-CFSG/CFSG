module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Rows
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NonbinaryApplication
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CatalogueCases

/-!
# Exhaustive B.5 comparison with the seven chosen-module alternatives

Every irreducible source row is compared on the literal moved/fixed quotient.
The three reducible source branches are reduced using Irr+; repeated natural
modules have multiplicity one. The remaining exits retain the exact rank-one
or nonbinary natural markings needed by the independent source producers.
Source: Aschbacher--Smith B.5.1 and 12.2.2, pp.99--103,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.ExtensionConsequences
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H] [Finite H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)
include c

/-- Exhaustive comparison of the actual B.4.2 list with the seven printed
12.2.2 alternatives. Only the existing rank-one and nonbinary source exits remain. -/
theorem irreducible_rows (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (s : MovedSection ρ K) (hi : IrreducibleAlternative K s) :
    ModuleAlternatives1222 D ∨
      (∃ F : BinaryField, Nonempty (ActionEquiv
        (s.action.comp K.subtype) (linearNatural F 2))) ∨
      (∃ F : BinaryField, 1 < F.degree ∧ NonbinaryRow s F) := by
  have hr := ModuleClassification.sourceRow_of_irreducible hi.source
  cases hr with
  | rankOne F e => exact Or.inr (Or.inl ⟨F,⟨e⟩⟩)
  | linearThree e => exact Or.inl (c.linearThree hq s hi.irrPlus e)
  | nonbinaryLinearThree F hF e => exact Or.inr (Or.inr ⟨F,hF,.linearThree e⟩)
  | symplectic F hF e => exact Or.inr (Or.inr ⟨F,hF,.symplectic e⟩)
  | g2 F hF e => exact Or.inr (Or.inr ⟨F,hF,.g2 e⟩)
  | derivedG2 e => exact Or.inl (c.derivedG2 hq s e)
  | alternating n hn hn' e => exact Or.inl (c.alternating s hn hn' e)
  | alternatingSevenFour e hd => exact Or.inl (c.alternatingSevenFour s hi e hd)
  | tripleSix a => exact Or.inl (c.tripleSix hq s hi a)
  | binaryLinear d hd e => exact Or.inl (c.binaryLinear hq s hi hd e)
  | exteriorFive e hd => exact Or.inl (c.exteriorFive hq s hi e hd)

/-- This comparison consumes all B.5.1(1) cases, including both repeated rows
and the natural-plus-dual row, on the literal chosen Irr+ space. -/
theorem source_rows (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (b : QuasisimpleSourceConclusion ρ K) :
    ModuleAlternatives1222 D ∨
      (∃ F : BinaryField, Nonempty (ActionEquiv
        (b.sectionData.action.comp K.subtype) (linearNatural F 2))) ∨
      (∃ F : BinaryField, 1 < F.degree ∧ NonbinaryRow b.sectionData F) := by
  have hr := c.source_irreducible_or_single b
  rcases hr with hi | ⟨d,hd,⟨e⟩⟩
  · exact c.irreducible_rows hq b.sectionData hi
  · have hp := c.projection_injective_of_binaryLinear hq hd e.groupEquiv
    exact Or.inl (.linear d (Or.inr hd) ((c.wholeMarking b.sectionData hp).trans e))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
