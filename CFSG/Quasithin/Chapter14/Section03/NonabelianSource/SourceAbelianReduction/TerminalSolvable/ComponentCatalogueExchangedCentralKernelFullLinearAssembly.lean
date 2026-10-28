module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelFullLinear
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernel

/-!
# The central-kernel consumer of the full-linear reduction

The native outer-Sylow bound and the original degree-four exclusion supply
properness of the literal constituent action. The existing central-kernel
consumer then constructs the faithful dual pair once its separate
nondegenerate exclusion is supplied. All three outstanding model inputs
are explicit; final source assembly must discharge them.

Source: Aschbacher--Smith G.10.15(2)(II),(3), printed pp.362--363.
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

/-- The actual central-kernel consumer, with its two full-linear obligations
and the independent nondegenerate exclusion still visible. -/
theorem faithful_data_of_outer_bound_four_not_nondegenerate
    (hbound : ∀ (_a : ElementaryOuterSylowAction (componentOrbit L ⊤))
      (_e : (componentOrbit L ⊤) ≃* LinearMap.GeneralLinearGroup (ZMod 2) I),
      finrank (ZMod 2) I = 4)
    (hfour : finrank (ZMod 2) I = 4 → ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hnot : ¬ (B.restrict I).Nondegenerate) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected :=
  s.faithful_data_of_proper_not_nondegenerate
    (s.not_fullLinear_of_outer_bound_and_four hbound hfour) hnot

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
