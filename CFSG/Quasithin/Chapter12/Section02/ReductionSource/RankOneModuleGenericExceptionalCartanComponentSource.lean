module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeComponentSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The original component branch in the chosen Chapter12 module

Apply the source 5.2.2 component sieve to the literal chosen module and
its prime Cartan actor. The original right factor is explicitly a
C-component of H, so changed-Sylow maximality applies at the original
Sylow T. The resulting containing component retains the strict quotient
embedding, the binary triality endpoint and the odd rank-one exclusions.

The hypotheses concerning the component and its non-A₅ quotient describe
the component branch of source 5.1.10(1); the parabolic-diagram and A₅
branches are separate source cases.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

theorem rankOne_prime_component_sylow_and_odd_exclusions
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
      (Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) →
        Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
        ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3) ∧
      (∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q) ∧
      ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  have hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.normalizingSylow_sylow_extension_of_component hi hH c hd hz hC hnot,
    d.component_source_overcomponent_odd_exclusions hi hH c hd hz hC hnot⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
