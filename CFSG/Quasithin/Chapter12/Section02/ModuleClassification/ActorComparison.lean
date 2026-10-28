module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Comparison
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor

/-!
# Projection identities for the chosen component image

This extension accesses the existing component-map implementation only to
publish its action formula. Clients then use that formula without unfolding
the nested image and quotient construction.
Source: Aschbacher--Smith 12.2.2, p.795.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

omit [Finite G] in
theorem componentHom_action (l : L) :
    D.seedRepresentation (D.componentHom l) = D.chosenAction l := by
  apply LinearMap.ext
  intro v
  rfl

theorem componentQuotientHom_action (q : L ⧸ pCore 2 L) :
    D.seedRepresentation (D.componentQuotientHom q) = D.quotientAction q := by
  induction q using QuotientGroup.induction_on with
  | H l =>
    exact (congrArg (fun k : D.componentImage => D.seedRepresentation k)
      (D.componentQuotientHom_mk l)).trans
        ((D.componentHom_action l).trans (D.quotientAction_mk l).symm)

noncomputable def seedComparison : D.LiteralComparison D.seedRepresentation D.componentImage where
  projection := D.componentQuotientHom
  surjective := D.componentQuotientHom_surjective
  faithful := (subspaceImageRepresentation_injective _ _).comp D.componentImage.subtype_injective
  action := D.componentQuotientHom_action

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
