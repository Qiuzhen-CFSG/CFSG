module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeChangedSylowAction

/-!
# The actual chosen-module changed-Sylow component branch

Apply the prime-actor component construction to the original chosen module.
At the smaller changed Sylow it produces a normal relative C-component,
a proper embedding in the literal two-core quotient, and exclusion of all
Bender containing models. In the other branch the changed subgroup is an
ambient Sylow subgroup. The remaining component-model exclusions and the
final Cartan normalization remain with the consolidated owner
qt-d-1222-rankone-cartan-local-to-global.

Source: Aschbacher--Smith 5.2.2, p.648, as used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B E L₂ : Subgroup G} (D : ChosenModule T L V)
include D

/-- The changed-Sylow branch with its actual component and quotient embedding. -/
theorem rankOne_prime_changedSylow_components
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (he : CartanPrimeActor A H p E)
    (d : Prime.LocalData T L H B E L₂)
    (hz : (Prime.generated L H E L₂).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (Prime.extension T L H B E L₂),
      let T₁ := (P : Subgroup (Prime.extension T L H B E L₂)).map
        (Prime.extension T L H B E L₂).subtype
      Prime.normalizingSylow T L₂ ≤ T₁ ∧
      T₁ ≤ normalizer ((E ⊔ Prime.normalizingSylow T L₂ : Subgroup G) : Set G) ∧
      ((T₁ = Prime.normalizingSylow T L₂ ∧
        let X := Prime.generated L H E L₂ ⊔ Prime.normalizingSylow T L₂
        ∃ K : Subgroup G, L₂ < K ∧ K ≤ X ∧
          (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
          (L₂.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) <
            (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) ∧
          ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K)) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) :=
  d.changedSylow_component_dichotomy
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH c he hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
