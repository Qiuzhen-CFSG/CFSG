module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Branches
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Contracts
public import CFSG.Quasithin.Chapter3.Section02.MinimalModuleSelection
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# Applying Hall faithfulness to the linear-three survivor

The survivor is nonnormal and its quotient has order 168, excluding A5.
Reselecting a minimal full module therefore lets the independent nonnormal
Hall-faithfulness theorem act on the original subgroup H intersect M.
Neither the local orbit nor its normalizer changes under this reselection.

Source: Aschbacher--Smith 10.2.3(2), printed pp.744--745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
open Chapter3.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

theorem survivor_nonnormal (s : SourceLinearThreeSurvivor T D) :
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
  fun h => s.exchange_moves (h s.exchange_mem)

theorem survivor_not_alternatingFive (s : SourceLinearThreeSurvivor T D) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr (s.quotient.symm.trans e).toEquiv
  rw [Matrix.PSL3Two.card_SL, nat_card_alternatingGroup] at hc
  norm_num [Nat.factorial] at hc

theorem survivor_hall_faithful (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hab : IsMulCommutative B)
    (hperm : (B.map H.subtype : Set G) * (T : Set G) =
      (T : Set G) * (B.map H.subtype : Set G)) :
    B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥ := by
  obtain ⟨E,hE⟩ := D.exists_minimal_fullModule
  have hlarge : 1 < ChapterE.generationParameter H := by rw [s.generation H hH]; decide
  exact hfaith hmany L E hE (survivor_nonnormal s) (survivor_not_alternatingFive s)
    H hH hlarge B hBM hB hab hperm

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
