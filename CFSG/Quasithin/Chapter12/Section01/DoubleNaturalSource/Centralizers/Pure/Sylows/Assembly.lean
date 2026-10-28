module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Five
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Orders.Other

/-!
# Ambient pure-point Sylows, orders and fusion in dimension five

The original marked Sylow assertion gives all three ambient centralizer
orders and preserves the literal dual summand in the point-Sylow control.
In dimension five, the permitted earlier positive weak-closure premise
discharges that assertion. The two-core argument of 12.1.6 remains a
separate obligation of this task, as does the dimension-four MS argument.

The final source owner is `qt-d-double-natural-centralizers`; it supplies
the H.9 model, nonsingular centralizers and earlier dimension-five weak
closure. No later dimension-four weak closure is used here.
Source: Aschbacher--Smith 12.1.4--6, printed pp.790--792.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal marked ambient Sylow statement supplies orders and fusion.
Its dimension-four proof remains with the pure-vector source owner. -/
theorem doubleNatural_pure_orders_sylows_fusion_of_marked_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedAmbientSylow D.sylow_normalizes_component →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureFusion := by
  let := D.doubledOrbit_elementary h
  intro S hc hs
  have ho := S.centralizerOrders_of_marked D.sylow_normalizes_component hc hs
  have hn := D.doubledOrbit_normalizer_eq h B.orbit_eq
  exact ⟨ho, S.purePointSylows_of_marked D.sylow_normalizes_component hn hs,
    B.pureFusion_of_centralizerOrders S hn ho⟩

/-- Positive earlier weak closure discharges the marked ambient Sylow premise. -/
theorem doubleNatural_pure_orders_sylows_fusion_of_globalW_pos_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureFusion := by
  let := D.doubledOrbit_elementary h
  intro S hc
  apply D.doubleNatural_pure_orders_sylows_fusion_of_marked_of_many h hmany B S hc
  intro w hw hp hfix
  exact (D.doubleNatural_marked_pure_sylow_of_globalW_pos_of_many
    h hmany B hW S w hw hp hfix).2

/-- The dimension-five 12.1.5 family uses only the permitted earlier inputs. -/
theorem doubleNatural_five_pure_orders_sylows_fusion_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureFusion :=
  D.doubleNatural_pure_orders_sylows_fusion_of_globalW_pos_of_many h hmany B hW

/-- In dimension five the only remaining local obligation is the two-core
argument; the order and Sylow callbacks have been discharged. -/
theorem doubleNatural_five_pure_conclusions_of_core_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers → B.PureCoreControl →
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S hc hcore
  obtain ⟨ho, hs, _⟩ := D.doubleNatural_five_pure_orders_sylows_fusion_of_many h hmany B hW S hc
  exact D.doubleNatural_pure_conclusions_of_orders_and_core_of_many h hmany B S ho hs hcore

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
