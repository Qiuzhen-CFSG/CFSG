module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CentralComparison
/-!
# The faithful central quotient in the alternating rows

The kernel calculation identifies L/C_L(V) with the actual B.5 component.
The fixed-quotient equivalence then gives the literal alternating-row action,
using the original projection on every l in L. No simple-quotient hypothesis
or assumption that the original action of L/O2(L) is faithful is needed.
Source: Aschbacher--Smith 12.2.2(3d,e), printed p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)

noncomputable def faithfulCentralMarking (s : MovedSection ρ K) :
    letI := D.actionCentralizer_normal
    ActionEquiv D.faithfulCentralAction (s.action.comp K.subtype) := by
  let := D.actionCentralizer_normal
  refine ⟨c.faithfulEquiv,(c.centralEquiv s).symm,?_⟩
  intro q v
  induction q using QuotientGroup.induction_on with
  | H l =>
    apply (c.centralEquiv s).symm_apply_eq.mpr
    change D.chosenCentralAction l v =
      c.centralEquiv s ((MovedSection.action ρ s)
        (c.projection (QuotientGroup.mk' (pCore 2 L) l)) ((c.centralEquiv s).symm v))
    exact (congrArg (D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l))
      ((c.centralEquiv s).apply_symm_apply v)).symm.trans
      (c.centralEquiv_intertwines s (QuotientGroup.mk' (pCore 2 L) l)
        ((c.centralEquiv s).symm v)).symm
end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
