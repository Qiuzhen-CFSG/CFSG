module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeQuinticSolvableCatalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeQuinticSolvableLocal

/-!
# The conditional quintic exclusion for the original chosen module

The actual selected pair inherits quasithinness from the unchanged Chapter
12 input. The full reduced catalogue filter contradicts its nonsolvable
right endpoint if p = 5, so the original prime actor has p = 3. The second
application constructs the source-selected pair and applies recognition at
that same pair, with the original sourceS, zero core and KnownSimple scope.

The only extra input is genuine reduced recognition. Its independent source
assembly producer must discharge it before the original theorem is complete.
Source: Aschbacher–Smith 5.2.2 and 12.2.2, pp.647–648 and 795; F.1.12,
pp.262–264, and DGS Theorem A, pp.99–100.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The literal chosen-module pair gives p ≠ 5 and hence p = 3 from the
full reduced catalogue; its quasithinness is inherited from the original input. -/
theorem rankOne_cartan_prime_ne_five_and_eq_three_of_reduced_alternatives
    {T : Sylow 2 G} {L V H A B D R : Subgroup G} {n p : ℕ}
    (C : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R) (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (ha : Global.OriginalExtension.ReducedAlternatives
      (D ⊔ Global.sourceS L H) R (Global.sourceS L H)) : p ≠ 5 ∧ p = 3 := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  have hfive := d.prime_ne_five_of_reduced_alternatives hi hH c hd hz ha
  exact ⟨hfive,hd.prime.resolve_right hfive⟩

/-- Apply catalogue filtering to the pair actually selected by the original
source construction. Only genuine reduced recognition remains explicit. -/
theorem rankOne_cartan_prime_eq_three_of_source_reduced_alternatives
    {T : Sylow 2 G} {L V H A B D : Subgroup G} {n p : ℕ}
    (C : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (ha : ∀ R : Subgroup G, LocalData T L H B D R → SelectedSourceModels H R →
      (generated L H D R).pCoreIn 2 = ⊥ →
      Global.OriginalExtension.ReducedAlternatives
        (D ⊔ Global.sourceS L H) R (Global.sourceS L H)) : p ≠ 5 ∧ p = 3 := by
  obtain ⟨R,d,hs,hz,_⟩ := C.rankOne_cartan_source_prime_pair_zero_core
    h hmany hn hpsl hH hgen hthree c hd
  exact C.rankOne_cartan_prime_ne_five_and_eq_three_of_reduced_alternatives
    h hmany hn hpsl hH c hd d hz (ha R d hs hz)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
