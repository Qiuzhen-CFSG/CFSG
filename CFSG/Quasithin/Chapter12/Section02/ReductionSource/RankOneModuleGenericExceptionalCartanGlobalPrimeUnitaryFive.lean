module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeUnitaryFive
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Chapter 12 exclusion of the smaller-Sylow unitary containers

Apply the original chosen-module input and both Cartan markings to the
unitary-five calculation. The literal quotient and relative normality
are retained: the selected right factor may be a parabolic local component.
The remaining A₅ catalogue loses both PSU₃(5) and its distinct SU₃(5) cover.

Source: Aschbacher–Smith 5.2.2, pp.648–649, applied in12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Exclude both odd-prime unitary containing rows for the original marked pair. -/
theorem rankOne_cartan_source_A5_unitary_exclusion
    {T : Sylow 2 G} {L V H A B D R K : Subgroup G} {n p q : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T L H B D R)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (P : Sylow 2 (extension T L H B D R))
    (hP : (P : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 q) : False := by
  exact d.changedSylow_A5_unitary_exclusion
    (C.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hgen hthree c hd hz hs P hP hKX hRK hK hKn hA5 hq ho hm

/-- The literal remaining catalogue after excluding both unitary rows. -/
theorem rankOne_cartan_source_A5_remaining_nonunitary
    {T : Sylow 2 G} {L V H A B D R K : Subgroup G} {n p : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T L H B D R)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (P : Sylow 2 (extension T L H B D R))
    (hP : (P : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hm : RemainingSourceContainer (generated L H D R ⊔ normalizingSylow T R) K) :
    let X := generated L H D R ⊔ normalizingSylow T R
    let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    A36Common I ∧
      ((IsComponent (X ⧸ pCore 2 X) I ∧ IsSimpleGroup I ∧
        (Nonempty (I ≃* Janko4.Model) ∨ ClassicalGroup.IsPSL I 3 5)) ∨
      A36Natural I ∨ A36Nilpotent I) := by
  exact d.changedSylow_A5_remaining_nonunitary
    (C.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hgen hthree c hd hz hs P hP hKX hRK hK hKn hA5 hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
