module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Complete

/-!
# The full corrected B.4.2 list on an original fixed-free choice

The faithful stabilizer image on the literal chosen space has the original
component image as its generalized Fitting subgroup. The original QTKE
hypotheses supply SQTK via the proved Theorem A. When C_V(L)=1, Irr⁺ makes
the component action irreducible, so the complete corrected B.4.2 theorem
applies to every FF witness on this actual seed actor.

This is a conditional branch of the 12.2.2 comparison, not its seven-case
conclusion. In particular an FF witness for the full linear normalizer is
not assumed to lie in this smaller actor.
Source: Aschbacher--Smith 3.2.8 and 12.2.2, printed pp.582 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Full model, action, offender and ratio data on the original fixed-free
seed, with all universal B.4.2 and A inputs discharged. -/
theorem seed_irreducible_actionCase
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hff : IsFFModule D.seedRepresentation) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
      D.seedRepresentation D.componentImage (offenderSubgroup D.seedRepresentation) := by
  apply ChapterB.SourceClassification.actionCase_of_source _ hff
  exact ChapterB.SourceClassification.source_hypotheses
    (D.seed_sqtk h (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple))
    (D.seed_fitting h.quasisimple) (D.componentImage_quasisimple h.quasisimple)
    (subspaceImageRepresentation_injective _ _) (D.seed_irreducible hc) hff

/-- The same application retains the literal acting quotient L/O₂(L) and
its original projective central quotient, even before its center is killed. -/
theorem seed_classification_with_original_quotient
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hff : IsFFModule D.seedRepresentation) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
      D.seedRepresentation D.componentImage (offenderSubgroup D.seedRepresentation) ∧
    Nonempty (((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      (D.componentImage ⧸ center D.componentImage)) :=
  ⟨D.seed_irreducible_actionCase h hc hff, ⟨D.componentCentralQuotientEquiv h.quasisimple⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
