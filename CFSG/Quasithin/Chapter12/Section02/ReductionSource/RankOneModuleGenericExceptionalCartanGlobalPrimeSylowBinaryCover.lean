module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowBinaryCover
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowBinaryTriality

/-!
# The whole binary triality quotient in the chosen-module branch

At the smaller changed Sylow, a rank-two containing component covers the
whole quotient of G₀T₀ by its own two-core. The original prime actor lies
in that component, which equals O²(G₀T₀), and inclusion induces the displayed quotient isomorphism.
This applies the cubic rank bound of the original generic Input and retains
both the marked right section and the alternative ambient Sylow subgroup.

Binary exclusion, source selection, higher-field reduction, other component
families and final normalization remain with
qt-d-1222-rankone-cartan-local-to-global. Source: Aschbacher–Smith 5.2.2,
printed pp.648–649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- The binary branch identifies the actual smaller quotient, including
its quotient map on the original containing component. -/
theorem rankOne_prime_changedSylow_binary_cover
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
        ∃ K : Subgroup G, R < K ∧ ∃ hKX : K ≤ X,
          (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
          (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
          (Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) →
            Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
            ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3 ∧
            D ≤ K ∧ K = residual X ∧ K ⊔ normalizingSylow T R = X ∧
            Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X) ∧
            ∃ e : (K ⧸ pCore 2 K) ≃* (X ⧸ pCore 2 X),
              ∀ k : K, e (QuotientGroup.mk' (pCore 2 K) k) = q (inclusion hKX k))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) :=
  d.changedSylow_binary_cover
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
