module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSmall
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowRee

/-!
# The small containing-family reduction for the chosen module

The original chosen module supplies the generic Input to the completed
small-family exclusions. The resulting witness retains the literal quotient,
relative component normality, the DT₀ action and the larger ambient-Sylow
alternative. Its rank-two containing-family branch is reduced to ³D₄(2),
and the binary ternary covering families are excluded at every exponent.

This supplies the small-model step in the changed-Sylow argument. The final
normalization and remaining source obligations stay with the consolidated
owner qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.2.2, pp.648–649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- Apply the small-family exclusions and full rank-two reduction to the
actual chosen module, with no added quotient-model or parabolic hypotheses. -/
theorem rankOne_prime_changedSylow_small_exclusions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D R),
      let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
      normalizingSylow T R ≤ T₁ ∧
      T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
      ((T₁ = normalizingSylow T R ∧
        let X := generated L H D R ⊔ normalizingSylow T R
        let q := QuotientGroup.mk' (pCore 2 X)
        ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
          (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
          (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
          ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
          ¬ (IsAlternating (K ⧸ pCore 2 K) 5 ∨ IsAlternating (K ⧸ pCore 2 K) 6 ∨
            IsAlternatingCover (K ⧸ pCore 2 K) 6) ∧
          (∀ k : ℕ, 1 ≤ k → ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
            IsSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨ IsSU (K ⧸ pCore 2 K) 3 (2 ^ k))) ∧
          (RankTwoTheoremC (K ⧸ pCore 2 K) →
            Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) :=
  d.changedSylow_small_exclusions
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
