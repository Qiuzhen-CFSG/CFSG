module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceAssembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceReversal.Ranks

/-!
# The source critical reversal in the original order-two conclusion

The original14.7.69 consumer now constructs its14.7.39/F.9.17 symmetry
internally from the same source Data and structural predecessor. Both U
and both point markings retain the actual right conjugator. The earlier
faithful/module classifications, local-control and weak-closure producers,
and the separate14.7.68 centralizer implication remain with their source
owners. No reversal or rank-selection callback is required.

Source: Aschbacher–Smith14.7.39 and14.7.69, pp.1060 and1072–1073.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08 ResidualNormalizer Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

theorem Data.order_two_of_source_reversal (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : LocalControl.Earlier14710.{u}) (weakClosure : Theorem14731.{u})
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H)
    (c : CriticalPath (L := L) F) (selection : c.RankSelection) :
    Nat.card (star F c.Uα) = 2 := by
  exact d.order_two_of_original_source structural faithful modules baumann weakClosure
    (SourceReversal.earlierSymmetry d structural) hcentralizer68 c selection
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
