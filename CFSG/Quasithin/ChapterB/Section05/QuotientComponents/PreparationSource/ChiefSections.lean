module

public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.ChiefSections.Actor
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.ChiefSections.Models
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.ChiefSections.Selection

/-!
# The complete existential chief-section branch of B.5.5

Starting with an original moving best offender and a normal component L,
choose a best offender A on the original V and one faithful irreducible
A-invariant L-chief section. The same literal actor (LA)/ker has generalized
Fitting subgroup equal to its marked L-image and a best offender contained
in its marked A-image. Apply the full corrected B.4.2 theorem to that actor,
then extract every model in B.5.5(1iv), including the cubic center and actual
central quotient in the triple-A₆ case.

The only retained classification inputs are the existing full A.2, A.3.6
and corrected B.4.2 implications, produced by `qt-a-02`,
`qt-a03-sqtk-structure` and `qt-b-04`. Their final discharge belongs to
`qt-b05-quotient-components`. The parent preparation theorem supplies
normality and the initial moving offender using its opening B.5.5 steps;
no section, fitting, model or action conclusion is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.5(1iii–iv), printed pp.104–105; B.4.2, printed p.86.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.PreparationSource
open SourceInduction ComponentReduction ComponentReduction.PreliminaryActions
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- B.5.5(1iii–iv): one original moving best offender and one faithful chief
section supply all the structural, offender, model and full B.4.2 clauses. -/
theorem chief [Finite D] {K : GroupClass.{u}}
    (hA : HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) {L A₀ : Subgroup D}
    (hL : IsComponent D L) [L.Normal]
    (hA₀ : IsBestOffender ρ A₀) (hm₀ : ⁅L,A₀⁆ = L) :
    ∃ A, IsBestOffender ρ A ∧ ⁅L,A⁆ = L ∧ Nonempty (Preparation.ChiefConclusion ρ A L) := by
  let := hyp.finite_module
  let := hL.2
  obtain ⟨A, hbest, hm, s, hb⟩ := ChiefSections.exists_chiefSection ρ hyp.faithful hyp.twoCore
    hL (component_center_order ρ hA h36 hyp hL) hA₀ hm₀
  let := hbest.1.2
  have hp : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  have ha := ChiefSections.classify h4 hyp s hp (component_sqtk ρ hA hyp hL) hb
  exact ⟨A, hbest, hm, ⟨{
    sectionData := s
    fitting := ChiefSections.fitting_eq_component s hp
    offender := hb
    model := ChiefSections.models_of_actions (ChiefSections.componentEquiv s) ha
    actions := ha }⟩⟩

end CFSG.Quasithin.ChapterB.PreparationSource
