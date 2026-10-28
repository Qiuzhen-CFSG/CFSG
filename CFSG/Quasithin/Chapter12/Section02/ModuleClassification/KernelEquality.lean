module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CentralComparison

/-!
# The original centralizer and two-core kernels

Injectivity of the recovered component projection identifies C_L(V) with
O2(L). Faithfulness on the literal central quotient similarly identifies
the original chosen-central-action kernel. Both identities concern the
given projections, without replacing L by an abstract central quotient.
Source: Aschbacher--Smith 12.2.2, p.795.
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
include c

theorem centralizer_eq_twoCore (hp : Function.Injective c.projection) :
    (centralizer (V : Set G)).subgroupOf L = pCore 2 L := by
  rw [← c.originalProjection_ker]
  exact (MonoidHom.ker_comp_of_injective _ _ hp).trans (QuotientGroup.ker_mk' _)

theorem centralKernel_eq_twoCore (s : MovedSection ρ K)
    (hf : Function.Injective ((MovedSection.action ρ s).comp K.subtype))
    (hp : Function.Injective c.projection) : D.chosenCentralAction.ker = pCore 2 L := by
  apply le_antisymm _ D.centralAction_core
  intro l hl
  apply (QuotientGroup.eq_one_iff l).mp
  apply c.centralAction_injective s hf hp
  exact hl.trans (map_one D.centralQuotientAction).symm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
