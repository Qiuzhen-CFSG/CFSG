module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreLeftAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalModuleComparison

/-!
# Original Sylow action in the escaping Cartan's prime pair

The existing small-generation and changed-Sylow arguments select an actual
zero-core prime pair. Its whole left parabolic contains T ∩ L in its
two-core. The original moved chosen module has exactly O₂(L) as its
centralizer there, and the resulting action has order 2ⁿ. Opposed Sylow
generation bounds its displacement by 2ⁿ, which also bounds the derived
subgroup of the left core from below.

This supplies structural data for the remaining mixed F.1.12 recognition
without a module model, amalgam marking or action premise. It keeps the
original Hall Cartans, residual, degree and literal sourceS, and does not
identify the selected factor with an actual component of H.
Source: Aschbacher--Smith 5.2.2, pp.647--648, and its original 12.2.2
application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The same escaping prime pair has a large derived left core, with the
original moved module's action kernel and degree proved internally. -/
theorem rankOne_cartan_prime_pair_left_core_action_of_escape
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
        let U := ⁅RankOneModule.wholeReduced T L,L⁆
        let Q := ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2
        (T : Subgroup G) ⊓ L ≤ Q ∧
        ((T : Subgroup G) ⊓ L) ⊓ centralizer (U : Set G) = L.pCoreIn 2 ∧
        (L.pCoreIn 2).relIndex ((T : Subgroup G) ⊓ L) = 2^n ∧
        2^n ≤ Nat.card (⁅U,(T : Subgroup G) ⊓ L⁆ : Subgroup G) ∧
        2^n ≤ Nat.card (⁅Q,Q⁆ : Subgroup G) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨hs,p,D,R,hd,d,hselected,hzero,hf⟩ :=
    C.rankOne_cartan_smallGeneration_and_prime_pair_of_escape
      h hmany hn hpsl hH hgen hthree c hcontrol hescape
  exact ⟨hs,p,D,R,hd,d,hselected,hzero,hf,
    d.original_sylow_le_left_parabolic_core hi hH c hd,
    hi.moved_sylow_centralizer,hi.moved_sylow_action_index,
    hi.moved_sylow_displacement_bound,d.left_parabolic_core_derived_bound hi hH c hd⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
