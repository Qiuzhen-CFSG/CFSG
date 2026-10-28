module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowRee
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowTriality

/-!
# Ree, triality, G₂ and classical exclusions for the chosen module's changed Sylow

The original chosen module supplies the generic Input. The source argument
then excludes large Ree and nonbinary genuine triality, G₂, symplectic-four, projective linear-three and
special linear-three models for the literal containing component in the smaller
changed-Sylow branch.
The two-core quotient, relative normality and larger ambient-Sylow alternative
are retained. The remaining component catalogue and final normalization
remain with qt-d-1222-rankone-cartan-local-to-global.

Source: Aschbacher--Smith 5.2.2, pp.648--649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- Apply the Ree, triality, G₂ and classical exclusions, including the special-linear cover,
to the actual changed-Sylow dichotomy. -/
theorem rankOne_prime_changedSylow_ree_exclusions
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
          ¬ ReeF4.IsReeF4Model (K ⧸ pCore 2 K) ∧
          ∀ k : ℕ, 2 ≤ k →
            ¬ (ClassicalGroup.IsPSp (K ⧸ pCore 2 K) 2 (2 ^ k) ∨
              ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
              Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
              ClassificationModels.IsG2At (K ⧸ pCore 2 K) (2 ^ k) ∨
              Triality.Standard.IsTrialityGroupAt (2 ^ k) (K ⧸ pCore 2 K))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) :=
  d.changedSylow_ree_exclusions
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
