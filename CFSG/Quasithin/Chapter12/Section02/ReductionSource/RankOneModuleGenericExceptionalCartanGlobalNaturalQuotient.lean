module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The original natural fixed quotient and escaping Cartan prime pair

A natural quotient of the original omega-span now suffices for degree two
or four and small Cartan generation. Its centralizer kernel is removed by
the zero-core common-normal argument, without a splitting or an additional
omega-centralization hypothesis. The constructed prime pair retains the
same Cartans, residual, Sylow and PSL3(4) exclusion, including the actual
component/parabolic distinction. Exhausting the source module alternatives
and recognizing the resulting zero-core pair remain with final assembly.

Source: Aschbacher--Smith 5.1.2, 5.1.6(2), 5.2.2 and 12.2.2,
pp.630,632,647,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The original natural fixed quotient gives degree two or four and the
actual escaping prime pair, with its central kernel discharged internally. -/
theorem rankOne_cartan_natural_quotient_degree_and_prime_pair_of_escape
    {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G))
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    (n = 2 ∨ n = 4) ∧ CartanSmallGeneration A H n ∧
      ∃ (p : ℕ) (D R : Subgroup G), CartanPrimeActor A H p D ∧
        LocalData T L H B D R ∧ SelectedSourceModels H R ∧
        (generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) := by
  let hi := C.rankOne_generic_input_of_many h hmany (by omega : 1 < n) hpsl
  have hz := hcontrol.core_eq_bot_of_not_normalizes le_rfl hescape
  obtain ⟨hdegree,hs⟩ := hi.natural_quotient_cartan_degree_and_smallGeneration hH hgen c hm hz
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hescape
  obtain ⟨R,d,hmodel,hzero,hf⟩ := source_prime_pair_zero_core hi hH hgen hthree c hd
  exact ⟨hdegree,hs,p,D,R,hd,d,hmodel,hzero,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
