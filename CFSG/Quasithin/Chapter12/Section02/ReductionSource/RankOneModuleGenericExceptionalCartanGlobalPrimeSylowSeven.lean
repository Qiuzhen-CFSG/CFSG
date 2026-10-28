module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSeven
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSmall

/-!
# The original seven-subgroup at the changed Sylow

In the remaining rank-two branch the literal B ∩ R has order seven and
embeds in R/O₂(R). It centralizes the prime actor and acts trivially on
the original L/O₂(L) for n = 2, 4, or 8. The latter assertion is expressed
by ambient commutators in L's embedded two-core, so both quotient maps
and the actual Hall subgroup survive in this chosen-module application.

This is a constraint on the binary triality endpoint, not its exclusion.
The original small-degree reduction and remaining module argument stay
with qt-d-1222-rankone-cartan-local-to-global. Source: Aschbacher–Smith
5.2.2, printed pp.648–649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- Apply the marked seven-subgroup calculation to the actual chosen Input
and changed-Sylow witness, keeping the original field bound explicit. -/
theorem rankOne_prime_changedSylow_seven_actor
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hsmall : n = 2 ∨ n = 4 ∨ n = 8)
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
          (RankTwoTheoremC (K ⧸ pCore 2 K) →
            Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
            ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3 ∧
            Nat.card (B ⊓ R : Subgroup G) = 7 ∧
            B ⊓ R ≤ centralizer (D : Set G) ∧
            Function.Injective ((QuotientGroup.mk' (pCore 2 R)).comp
              (inclusion (show B ⊓ R ≤ R from inf_le_right))) ∧
            ∀ b ∈ B ⊓ R, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ L.pCoreIn 2)) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) :=
  d.changedSylow_seven_actor
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hsmall hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
