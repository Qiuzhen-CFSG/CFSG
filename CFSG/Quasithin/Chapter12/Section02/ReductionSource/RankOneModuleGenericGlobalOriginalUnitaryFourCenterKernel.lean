module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourCenterKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourAction

/-!
# Original U₄ point-center fixation in the Chapter 12 setup

The actual right join-core acts trivially on the point-residual quotient.
Its two-power-order action therefore fixes Z(R), by the native scalar-kernel
calculation. The original normalized-Borel factorization extends this to S.
Both applications retain the arbitrary selected perfect R and the broad
original marking, before any degree bound or full comparison.

Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6--7, pp.650--651,
and the literal Chapter 12 setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
  (hp : Group.IsPerfect R) (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (e : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H))
include D h hmany hn hpsl hH d hp e

/-- The literal original enlarged right core fixes the selected point center. -/
theorem rankOne_global_original_unitaryFour_core_centralizes_center :
    (R ⊔ Global.sourceS L H).pCoreIn 2 ≤
      centralizer ((center R).map R.subtype : Set G) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_core_centralizes_center hi hH.1.1.2 hp m hm point e

/-- Every element of the original S fixes the same entire selected center. -/
theorem rankOne_global_original_unitaryFour_source_centralizes_center :
    Global.sourceS L H ≤ centralizer ((center R).map R.subtype : Set G) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_source_centralizes_center hi hH.1.1.2 hp m hm point e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
