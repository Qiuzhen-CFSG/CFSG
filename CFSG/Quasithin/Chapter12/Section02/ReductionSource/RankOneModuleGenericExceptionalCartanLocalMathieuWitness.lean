module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieuWitness
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalRecognition

/-!
# The original Chapter 12 escape in the selected M₂₃ row

The same normal containing component now supplies the complete local
witness, with its escaping cubic inverted by the original Sylow. Apply
whole-module recognition and relative omega-centralizer relocation to it.
The final application retains the original whole reduced subgroup and
also recovers the original chosen A5-module and field degree.

This proves the three-group-action branch of the selected M₂₃ row. The
original action is cyclic; its order three and the actual inverted cubic are
derived. Excluding the other action primes, exhaustive container selection
and binary-triality exclusion remain obligations of the original local sieve.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.637--638,795,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The actual selected M₂₃ component and original inverted cubic witness. -/
theorem rankOne_local_cartan_mathieu_twentyThree_witness_of_three_action
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23))
    (hthree : IsPGroup 3 ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C)))) :
    ∃ D : Subgroup G, LocalCartanWitness T H A Y (C.map Y.subtype) D := by
  exact LocalSieve.mathieu_twentyThree_local_witness_of_three_action
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKT hKL horbit hY hescape C hC hKC hm hthree

/-- Full original whole-module and chosen-module conclusions in the M₂₃ row. -/
theorem rankOne_local_cartan_mathieu_twentyThree_exceptional_of_three_action
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23))
    (hthree : IsPGroup 3 ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C)))) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      IsConjugationModel L V a5Module := by
  have hi := a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨_,he⟩ := LocalSieve.mathieu_twentyThree_cartan_exceptional_of_three_action hi
    hH hgen c hKT hKL horbit hY hescape C hC hKC hm hthree
  have hex := RankOneModule.exceptional_of_cartan_conclusion he
  exact ⟨he,hex,a.rankOne_exceptional_module_and_exponent hn hpsl hex⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
