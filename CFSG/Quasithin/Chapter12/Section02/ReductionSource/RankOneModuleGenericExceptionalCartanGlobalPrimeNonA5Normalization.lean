module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeNonA5Normalization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Chapter 12 application of non-A₅ changed-Sylow normalization

This is the literal Chapter 12 consumer for the non-A₅ row of the
changed-Sylow argument.  It retains the selected subgroup, its original Hall
markings and the actual extension map; only the maximality conclusion is
transported from Chapter 6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

theorem rankOne_cartan_source_nonA5_changedSylow_eq
    {T : Sylow 2 G} {L V H A B D : Subgroup G}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D)
    {R : Subgroup G} (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hR : R ∈ Chapter1.L G (T : Subgroup G))
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map
        (extension T L H B D R).subtype) :
    (P : Subgroup (extension T L H B D R)).map
        (extension T L H B D R).subtype = normalizingSylow T R := by
  let hinput := C.rankOne_generic_input_of_many
    h hmany hn hpsl
  exact d.nonA5_changedSylow_eq_normalizingSylow hinput hH c hd hz hR hnot P hTP

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
