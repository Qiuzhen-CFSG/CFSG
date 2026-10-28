module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowBinaryHall
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowBinaryCover

/-!
# Seven-rank exclusions at the changed Sylow

The original chosen-module input supplies the Hall-rank contradiction in
the smaller changed-Sylow branch. For each of the genuine PSL₃, SL₃ and
Sp₄ residual alternatives, the actual changed Sylow has either a containing
component outside the entire rank-two family, or is an ambient Sylow.
The binary endpoint is excluded using two independent seven-directions in
the original Hall subgroup and its action on ³D₄(2) with seven-free kernel.

For an actual non-A₅ H-component, the full-Sylow comparison is already
proved and the containing-component witness now excludes rank two,
odd-prime PSL₂ and J₁ together.

The zero-core recognition, higher-field reduction, other containing families
and full normalization remain with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.2.2, printed pp.648–649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- Apply the exclusion to the actual changed Sylow and the original residual,
retaining both genuine linear covering alternatives. -/
theorem rankOne_prime_changedSylow_classical_residual_excludes_rankTwo
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T L H B D R)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
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
          ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K)) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) :=
  d.changedSylow_classical_residual_excludes_rankTwo
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH hgen c hd hz hf hm

/-- The actual non-A₅ H-component branch excludes all rank-two
containing models, including binary triality, on its constructed witness. -/
theorem rankOne_prime_component_sylow_and_rankTwo_exclusions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    Chapter1.IsSylowIn 2 (normalizingSylow T R) (extension T L H B D R) ∧
    let X := generated L H D R ⊔ normalizingSylow T R
    let q := QuotientGroup.mk' (pCore 2 X)
    ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
      (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
      (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
      ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
      (∀ k : ℕ, 1 ≤ k → ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
        Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
        Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 (2 ^ k))) ∧
      ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) ∧
      (∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q) ∧
      ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  have hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.normalizingSylow_sylow_extension_of_component hi hH c hd hz hC hnot,
    d.component_source_overcomponent_rankTwo_exclusion hi hH c hd hz hC hnot⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
