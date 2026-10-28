module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelFullLinearFourReduction
public import Theory.SpecificGroups.BinaryLinear.FourOuterSylowActor

/-!
# Exclusion of degree four in the original exchanged full-linear branch

The original representation geometry and small-actor equality make X have
order eight. Under the literal full constituent action, its conjugation on
GL₄(2) is outer. Normality in the original Sylow forces its order to be at
least sixteen, by the checked eight-point Sylow calculation. This contradiction
supplies the degree-four input of `not_fullLinear_of_outer_bound_and_four`.

Source: Aschbacher--Smith G.10.15(3), printed p.363, retaining the original
small-actor hypothesis from 14.3.12, printed p.993.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource

/-- The original exchanged central-kernel constituent cannot induce the full
binary linear group in degree four. All source hypotheses and maps are retained. -/
theorem not_fullLinear_four {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc : Subgroup G}
    {F : InvariantFlag T (rankTwoSeed T M) 2}
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (s : ExchangedCentralSource T M Mc F g B v L I)
    (hd : finrank (ZMod 2) I = 4) :
    ¬ Function.Surjective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom := by
  apply s.not_fullLinear_four_of_outer_rank hd
  intro e x ho
  let := componentOrbit_top_normal L
  exact BinaryLinear.FourOuterSylowActor.normal_elementary_outer_actor_card
    (componentOrbit L ⊤) (pointSylow (F := F)) (F.terminalDot (F.X g))
    s.actor_sylow.1 s.actor_sylow.2 hd e x ho

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
