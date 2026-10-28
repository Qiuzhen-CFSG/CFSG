module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Rows
-- Intentional implementation/proof split: publish the quotient formulas
-- without exposing the implementation bodies of these action equivalences.
import all CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CentralComparison
import all CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FaithfulComparison
import all CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Rows

/-!
# Projection formulas for the literal module markings

Every recovered marking uses the original quotient map. These equations
make the commutative squares available to consumers without unfolding the
marking definitions. In particular the two-core and relative-centralizer
quotients induce the same action on the actual fixed-space quotient.
Source: Aschbacher--Smith 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

theorem faithfulCentralAction_comp_coreToFaithful : letI := D.actionCentralizer_normal
    D.faithfulCentralAction.comp D.coreToFaithful = D.centralQuotientAction := by
  let := D.actionCentralizer_normal
  apply MonoidHom.ext
  intro q
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  rfl

namespace LiteralComparison
open ChapterB.QuasisimpleSource
variable {D} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)

@[simp] theorem quotientMarking_groupEquiv (s : MovedSection ρ K)
    (hp : Function.Injective c.projection) (q : L ⧸ pCore 2 L) :
    (c.quotientMarking s hp).groupEquiv q = c.projection q := by rfl

@[simp] theorem wholeMarking_groupEquiv (s : MovedSection ρ K)
    (hp : Function.Injective c.projection) (q : L ⧸ pCore 2 L) :
    (c.wholeMarking s hp).groupEquiv q = c.projection q := by rfl

@[simp] theorem wholeCentralMarking_groupEquiv (s : MovedSection ρ K)
    (hs : IsCompl s.space.toSubmodule (fixedSpace ρ K))
    (hp : Function.Injective c.projection) (q : L ⧸ pCore 2 L) :
    (c.wholeCentralMarking s hs hp).groupEquiv q = c.projection q := by rfl

@[simp] theorem faithfulCentralMarking_groupEquiv_mk (s : MovedSection ρ K) (l : L) :
    letI := D.actionCentralizer_normal
    (c.faithfulCentralMarking s).groupEquiv
      (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) =
      c.projection (QuotientGroup.mk' (pCore 2 L) l) := by rfl

end LiteralComparison
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
