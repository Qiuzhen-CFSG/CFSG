module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalModule
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Full Cartan module recognition on the original Chapter 12 layer

At degree two, a centralizing local Cartan witness identifies the entire
commutator layer of R₂(LT), including its splitting and one/two multiplicity.
With the remaining sieve and A₇ exclusion, the actual double-sieve relocation
also yields the exceptional exit and the original chosen-module marking.
The original universal Cartan owner retains those two implications and the
degree-two argument; neither is hidden in a module-recognition assumption.

Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- Recognition on the actual whole layer once the component centralizes omega. -/
theorem rankOne_local_cartan_module_of_centralizes_degree_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X C)
    (hXC : X ≤ omegaCentralizer T) :
    Chapter6.Source.IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L) :=
  d.module_of_exponent_eq_two
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by decide : 1 < 2) hpsl)
    hH c hXC rfl

/-- The literal exceptional exit at degree two has no remaining module-recognition premise. -/
theorem rankOne_exceptional_local_cartan_of_sieve_a7_degree_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (ha7 : LocalCartanA7Exclusion G) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  have he := localCartan_escape_of_sieve_a7_degree_two hsieve ha7
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by decide : 1 < 2) hpsl)
    hH hgen c hY hescape
  have hex := RankOneModule.exceptional_of_cartan_conclusion he
  exact ⟨he,hex,(D.rankOne_exceptional_module_and_exponent (by decide : 1 < 2) hpsl hex).2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
