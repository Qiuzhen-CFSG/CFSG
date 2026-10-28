module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreOpposite
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalModuleComparison

/-!
# The opposite two-core in the original escaping prime pair

The source construction selects the same zero-core pair with its original
Hall subgroups and literal sourceS. In every binary-linear right row, the
derived subgroup of the full left two-core lies strictly inside the full
right two-core. Its order is at least 2ⁿ, the right core has order at least
2^(n+1), and its normalizer in the selected right factor is exactly the
original right Borel. All these action and kernel conclusions are derived;
no additional normality, core placement or equality of field degrees is
assumed. Exhaustive mixed F.1.12 recognition remains separate.

Source: Aschbacher--Smith 5.2.2, printed pp.647--648, using F.1.3 and
F.1.9, pp.260--262, with its 12.2.2 application on p.795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The original zero-core prime pair supplies the opposite-core placement
and exact right normalizer in each binary-linear quotient row. -/
theorem rankOne_cartan_prime_pair_opposite_core_of_escape
    {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) :
    CartanSmallGeneration A H n ∧
      ∃ (p : ℕ) (D R : Subgroup G), CartanPrimeActor A H p D ∧
        LocalData T L H B D R ∧ SelectedSourceModels H R ∧
        (generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) ∧
        ∀ f : ℕ, ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f) →
          let S := Global.sourceS L H
          let P := (D ⊔ S) ⊔ (B ⊓ R)
          let Q := P.pCoreIn 2
          let N := ⁅Q,Q⁆
          2^n ≤ Nat.card N ∧ N ≠ ⊥ ∧
            N < (R ⊔ S).pCoreIn 2 ∧ 2^(n+1) ≤ Nat.card ((R ⊔ S).pCoreIn 2) ∧
            P ≤ normalizer (N : Set G) ∧
            R ⊓ normalizer (N : Set G) = (S ⊓ R) ⊔ (B ⊓ R) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨hs,p,D,R,hd,d,hselected,hzero,hf⟩ :=
    C.rankOne_cartan_smallGeneration_and_prime_pair_of_escape
      h hmany hn hpsl hH hgen hthree c hcontrol hescape
  exact ⟨hs,p,D,R,hd,d,hselected,hzero,hf,
    fun _ hlin => d.zeroCore_left_derived_opposite_core hi hH c hd hzero hlin⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
