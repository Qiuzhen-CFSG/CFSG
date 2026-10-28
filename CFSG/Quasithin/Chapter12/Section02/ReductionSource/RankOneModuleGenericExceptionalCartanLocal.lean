module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartan

/-!
# The relocated local Cartan argument on the Chapter 12 module

The generic input uses the actual whole reduced subgroup R₂(LT). The local
component sieve and the omega-centralization argument give the exceptional
exit through the relocation theorem. Restriction then identifies the
original chosen module and forces n=2. Neither assertion is an input.

The global application supplies this same universal local implication to
the existing 5.2.2 assembly, so it remains available at a changed Sylow
subgroup. The source sieve and centralization arguments remain unproved
premises, along with the independent preparation and global argument.

Source: Aschbacher--Smith, 5.1.13, 5.2.2 and 12.2.2,
printed pp.635--638,646--649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The original local escape, with the two earlier arguments explicit,
acts on the whole reduced layer and recovers the chosen A₅ marking. -/
theorem rankOne_exceptional_local_cartan_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    {A B Y : Subgroup G} (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (hcentral : LocalCartanCentralization KnownSimple.IsKnownSimple G) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  have hs := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  have he := sourceLocalCartanEscape_of_sieve_and_centralization hsieve hcentral
    T L (RankOneModule.wholeReduced T L) n hs H hH hgen A B c Y hY hescape
  have hex := RankOneModule.exceptional_of_cartan_conclusion he
  exact ⟨he, hex, D.rankOne_exceptional_module_and_exponent hn hpsl hex⟩

/-- The universal local relocation is supplied to the unchanged global
assembly. The global owner can use it for every Sylow and module choice. -/
theorem rankOne_exceptional_cartan_of_local_steps
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
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (hcentral : LocalCartanCentralization KnownSimple.IsKnownSimple G)
    (hglobal : SourceLocalCartanEscape KnownSimple.IsKnownSimple G →
      Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        CartanLocalControl A H → A ≤ normalizer (residual H : Set G)) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module :=
  D.rankOne_exceptional_cartan_of_source h hmany hn hpsl hH hgen hthree hescape
    hprepare (sourceLocalCartanEscape_of_sieve_and_centralization hsieve hcentral) hglobal

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
