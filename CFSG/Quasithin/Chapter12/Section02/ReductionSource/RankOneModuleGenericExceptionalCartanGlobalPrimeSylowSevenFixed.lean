module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSevenFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSeven

/-!
# Fixed lifts for the original seven-actor in Chapter 12

The literal centralizer C_L(B ∩ R) covers the original left quotient,
and its own two-core quotient is identified with L/O₂(L) by inclusion.
It already generates the full L-orbit of the original omega-center.
Thus fixing that center is equivalent to fixing the whole omega-module.
The field parameter here is the original n, independent of the triality
arm parameter. The binary exclusion still requires its source geometry.

Source: Aschbacher–Smith 5.2.2, printed p.648, used in 12.2.2, p.795.
The small-degree and remaining fixed-center/module premises, other component
families and final normalization stay with
qt-d-1222-rankone-cartan-local-to-global.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- Retain the actual changed Sylow and centralizer quotient marking in the
chosen-module application, with no new centralizer-covering premise. -/
theorem rankOne_prime_changedSylow_seven_fixed_lifts
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
          (Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) →
            Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
            ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3 ∧
            Nat.card (B ⊓ R : Subgroup G) = 7 ∧
            let E := B ⊓ R
            let C := L ⊓ centralizer (E : Set G)
            ∃ e : (C ⧸ pCore 2 C) ≃* (L ⧸ pCore 2 L),
              (∀ x : C, e (QuotientGroup.mk' (pCore 2 C) x) =
                QuotientGroup.mk' (pCore 2 L) (inclusion inf_le_left x)) ∧
              conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L =
                conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C ∧
              (E ≤ centralizer
                (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G) ↔
                E ≤ omegaCentralizer T))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) :=
  d.changedSylow_seven_fixed_lifts
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hsmall hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
