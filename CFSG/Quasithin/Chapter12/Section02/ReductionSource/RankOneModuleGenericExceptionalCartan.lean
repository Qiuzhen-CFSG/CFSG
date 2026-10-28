module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptional

/-!
# Applying the generic Cartan construction to the original Chapter 12 setup

The actual whole reduced subgroup supplies `RankOneGeneric.Input`.
Solvable-intersection preparation constructs both compatible Hall subgroups.
The local 5.1.13 implication and the local-to-global 5.2.2 implication then
give the exceptional module and relative component through the literal
ambient embeddings. Restriction to the chosen Irr⁺ subgroup also recovers
n = 2; no such marking or exponent is a hypothesis.

The three earlier source implications remain explicit and have separate
producers. These applications do not claim to complete 5.2.2 or 5.2.3.
Source: Aschbacher--Smith, printed pp.631--638,646--649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

namespace RankOneModule

omit [Finite G] in
/-- The exact generic source output supplies the existing exceptional exit,
using the same ambient component and its actual quotient isomorphism. -/
theorem exceptional_of_cartan_conclusion
    (he : CartanExceptionalConclusion T L (wholeReduced T L) H) :
    ExceptionalExit T L H := by
  obtain ⟨hmodule, hlinear, X, hRX, hXC, hcomponent, hmodel⟩ := he
  exact exceptional_of_ambient_component hmodule hlinear hXC hcomponent hRX hmodel

end RankOneModule

namespace ChosenModule
variable (D : ChosenModule T L V)
include D

/-- Original-source application of the compatible-Hall construction and
the two Cartan escape steps. The three named earlier implications are
genuine remaining proof obligations, not fields of the chosen setup. -/
theorem rankOne_exceptional_cartan_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hescape : ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G))
    (hprepare : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H → CartanPreparation T L H)
    (hlocal : SourceLocalCartanEscape KnownSimple.IsKnownSimple G)
    (hglobal : SourceLocalCartanEscape KnownSimple.IsKnownSimple G →
      Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        CartanLocalControl A H → A ≤ normalizer (residual H : Set G)) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  have hs := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨A, B, c⟩ := (hprepare hs hH hgen).exists_cartanPair
  have he := cartan_exceptional_of_local_and_global c hs.sylow_normalizes hH.1.1.2
    hescape (hlocal T L (RankOneModule.wholeReduced T L) n hs H hH hgen A B c)
      (hglobal hlocal hs hH hgen hthree A B c)
  have hex := RankOneModule.exceptional_of_cartan_conclusion he
  exact ⟨he, hex, D.rankOne_exceptional_module_and_exponent hn hpsl hex⟩

end ChosenModule
end CFSG.Quasithin.Chapter12.Section02
