module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeJankoFourNonA5
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Zero-core or strictly larger Sylow for the original Cartan prime pair

Apply the full J₄ recognition through the literal containing image and its
Sylow intersection. Together with the completed source sieve, this excludes
every smaller-Sylow row for the same original selected pair. Zero-core
recognition and the larger-Sylow component/parabolic alternatives remain,
with the original Cartans, residual, Hall markings and actual Sylow placement.

Source: Aschbacher–Smith5.2.2, pp.648–649, applied in12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The literal J₄ container forces PSL₂(4) for the same selected right quotient. -/
theorem rankOne_cartan_source_janko_four_right_four
    {T : Sylow 2 G} {L V H A B D R X K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R)
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hm : let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      Nonempty (I ≃* Janko4.Model)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := by
  exact d.source_overcomponent_janko_four_right_four
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz hs hSyl hRX hKX hRK hK hm

/-- The original prime pair has only the zero-core and strictly larger
changed-Sylow branches. Every smaller-Sylow container has been excluded. -/
theorem rankOne_cartan_source_zero_or_largerSylow
    {T : Sylow 2 G} {L V H A B D : Subgroup G} {n p : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧ RemainingLargerSource H R p n)) := by
  exact source_prime_pair_zero_or_largerSylow
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH hgen hthree c hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
