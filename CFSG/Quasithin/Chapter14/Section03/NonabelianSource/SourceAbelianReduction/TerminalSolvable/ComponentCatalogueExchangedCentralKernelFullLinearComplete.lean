module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelFullLinearDegreeReduction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelFullLinearFour
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernel
public import Theory.SpecificGroups.BinaryLinear.ElementaryOuterSylowMatrices

/-!
# Full-linear exclusion for the original exchanged central-kernel constituent

The literal outer Sylow action forces constituent degree four by the checked
graph-Sylow matrix calculation. The original small-actor geometry excludes
that degree, so the constituent image is proper. This discharges both source
premises of the earlier full-linear reduction without changing the selected
constituent, its central kernel, or the original ambient hypotheses.

The final faithful-dual-pair consumer now retains only the nondegenerate
constituent exclusion. Its G.12 recognition and classical-model obligations
remain with the central-kernel assembly owner; this module proves the
full-linear branch, not that remaining exclusion.

Source: Aschbacher--Smith G.10.15(3), printed p.363, with the original
14.3.12--15 small-actor hypotheses, printed pp.993--994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

include s

/-- The original constituent degree bound, with the graph-Sylow premise proved. -/
theorem fullLinear_degree
    (a : ElementaryOuterSylowAction (componentOrbit L ⊤))
    (e : (componentOrbit L ⊤) ≃* LinearMap.GeneralLinearGroup (ZMod 2) I) :
    finrank (ZMod 2) I = 4 :=
  s.fullLinear_degree_of_graphSylowDegreeBound
    BinaryLinear.ElementaryOuterSylow.graphSylowDegreeBound a e

/-- G.10.15(3) in the original exchanged central-kernel branch: the actual
selected constituent does not have the full linear action. -/
theorem not_fullLinear :
    ¬ Function.Surjective (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation.asGroupHom :=
  s.not_fullLinear_of_outer_bound_and_four s.fullLinear_degree s.not_fullLinear_four

/-- The literal faithful-dual-pair consumer, now requiring only the remaining
nondegenerate-constituent exclusion. Final discharge stays with the
`qt-e-14315-exchanged-central-kernel` assembly owner. -/
theorem faithful_data_of_not_nondegenerate (hnot : ¬ (B.restrict I).Nondegenerate) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected :=
  s.faithful_data_of_proper_not_nondegenerate s.not_fullLinear hnot

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
