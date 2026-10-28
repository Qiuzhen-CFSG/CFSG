module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalParabolicDegree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Parabolic field comparison in the chosen-module Cartan argument

The selected right factor's intrinsic PSL₂ degree determines the original
SL₃ or Sp₄ residual degree. For original left degree two, four or eight,
divisibility into this selected degree gives the actual Cartan normalization
conclusion. The nonzero-core application derives strict containment itself.

At the smaller changed Sylow, the same literal comparison excludes every
rank-two containing component when the original residual field degree is
even, including the previously remaining binary triality endpoint.
The full local-to-global assembly and its other source branches remain with
qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.2.2, pp.648–649, applied to 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (M : ChosenModule T L V)
include M

/-- The actual normalization conclusion with the selected parabolic marking. -/
theorem rankOne_cartan_normalizes_of_rankTwo_matching_small_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f m : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (d : LocalData T L H B D R) (hR : R < residual H) (hf : 1 < f) (hnm : n ∣ m)
    (hm : Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hr : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ m)) :
    A ≤ normalizer (residual H : Set G) :=
  d.cartan_normalizes_of_rankTwo_matching_small_degree
    (M.rankOne_generic_input_of_many h hmany (by omega) hpsl)
    hH hgen c hcontrol hn hnm hR hf hm hr

/-- A nonzero generated core supplies the strict selected-factor inclusion. -/
theorem rankOne_cartan_rankTwo_prime_excluded_of_matching_small_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f m : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (d : LocalData T L H B D R) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hf : 1 < f) (hnm : n ∣ m)
    (hm : Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hr : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ m)) : False :=
  d.rankTwo_prime_excluded_of_matching_small_degree
    (M.rankOne_generic_input_of_many h hmany (by omega) hpsl)
    hH hgen c hcontrol hn hnm hd hz hf hm hr

/-- Even original residual degree removes the binary triality endpoint as well. -/
theorem rankOne_cartan_not_rankTwo_container_of_even_residual_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (d : LocalData T L H B D R)
    (hd : CartanPrimeActor A H p D) (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    {K : Subgroup G} (hRK : R < K)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hf : 1 < f) (heven : Even f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) :=
  d.source_not_rankTwo_container_of_even_residual_degree
    (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH c hd hz hSyl hRK hKX hK hKn hf heven hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
