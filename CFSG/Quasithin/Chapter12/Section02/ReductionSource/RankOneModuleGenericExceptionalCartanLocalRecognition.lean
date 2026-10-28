module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Complete local module recognition on the original Chapter 12 action

The actual component witness now forces degree two and the full exceptional
conclusion on R₂(LT), without a supplied natural or Hermitian marking or any
chosen-module invariance premise. Restriction recovers the original chosen
A₅ action. The local escape and its global consumer retain only the original
component-and-inverted-cubic sieve as the local source premise; preparation
and the independent global argument remain explicit in the latter.

Source: Aschbacher--Smith 5.1.3, 5.1.13 and 5.2.2,
printed pp.630--631,635--638,646--649, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The original component witness settles every module row for the literal
whole reduced action and the original chosen constituent. -/
theorem rankOne_local_cartan_escape_of_witness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    {A B Y X C : Subgroup G} (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    n = 2 ∧ CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  obtain ⟨he,hout⟩ := localCartan_escape_of_witness
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY d
  have hx := RankOneModule.exceptional_of_cartan_conclusion hout
  exact ⟨he,hout,hx,(D.rankOne_exceptional_module_and_exponent hn hpsl hx).2⟩

/-- The original local-source application with the centralization and module
premises discharged. The actual component sieve is still required. -/
theorem rankOne_exceptional_local_cartan_of_sieve
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    {A B Y : Subgroup G} (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module :=
  D.rankOne_exceptional_local_cartan_of_source h hmany hn hpsl hH hgen c hY
    hescape hsieve localCartan_centralization

/-- The universal local implication is available at the changed Sylow choice
in the original global assembly. Its only local prerequisite is the sieve. -/
theorem rankOne_exceptional_cartan_of_sieve
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
    hprepare (sourceLocalCartanEscape_of_sieve hsieve) hglobal

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
