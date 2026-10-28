module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSubmodule
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNaturalQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalHermitian

/-!
# The remaining local module rows on the original Chapter 12 action

Thompson movement of the whole reduced action now gives the original
exceptional conclusion and chosen A₅ marking. A single actual nonzero
Sylow-invariant Hermitian subgroup gives the same conclusion without
containing all of omega. The natural central-quotient row is excluded with
its exact fixed kernel retained, also on the literal omega-span.

Above degree two, Thompson therefore centralizes the whole reduced action
and omega-span. Exhaustive recognition in that branch and the original
component-and-cubic sieve remain with the universal source assembly.
Source: Aschbacher--Smith 5.1.2--3 and 5.1.13, pp.630--631,638,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Representation.OrthogonalFourMinus
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C U : Subgroup G}
  (D : ChosenModule T L V)
include D
local instance (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))

/-- A Hermitian subgroup completes the conclusion for the original whole
reduced action, including the original chosen module's actual marking. -/
theorem rankOne_local_cartan_escape_of_hermitian_subgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (s : ℕ) [NeZero s]
    (hU : IsElementaryAbelian 2 U) (hUT : U ≤ (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) (hU0 : U ≠ ⊥)
    (hm : Chapter6.Source.IsConjugationModel L U (Representation.SL2.BinarySmall.hermitian s)) :
    n = 2 ∧ CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  obtain ⟨he,hout⟩ := localCartan_escape_of_hermitian_subgroup
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY d s hU hUT hTU hU0 hm
  have hx := RankOneModule.exceptional_of_cartan_conclusion hout
  exact ⟨he,hout,hx,(D.rankOne_exceptional_module_and_exponent hn hpsl hx).2⟩

/-- Thompson movement settles the original FF branch without a supplied
natural or symmetric-five module marking. -/
theorem rankOne_local_cartan_escape_of_thompson_moves
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (RankOneModule.wholeReduced T L : Set G)) :
    n = 2 ∧ CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  obtain ⟨he,hout⟩ := localCartan_escape_of_thompson_moves
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hj
  have hx := RankOneModule.exceptional_of_cartan_conclusion hout
  exact ⟨he,hout,hx,(D.rankOne_exceptional_module_and_exponent hn hpsl hx).2⟩

/-- The only higher-degree inputs have Thompson centralizing both the
whole original action and the actual omega-span. -/
theorem rankOne_local_cartan_thompson_centralizes_of_degree_gt_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 2 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (RankOneModule.wholeReduced T L : Set G) ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) :=
  localCartan_thompson_centralizes_of_degree_gt_two
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by omega) hpsl)
    hH hgen c hY d hn

/-- The actual natural central quotient is impossible on the original
whole reduced subgroup and its literal commutator layer. -/
theorem rankOne_local_cartan_not_natural_fixed_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n m : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    (¬ Chapter6.Source.IsNaturalFixedQuotient L (RankOneModule.wholeReduced T L) m) ∧
      (¬ Chapter6.Source.IsNaturalFixedQuotient L (RankOneModule.commutatorLayer T L) m) :=
  localCartan_not_natural_fixed_quotient
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d

/-- Source row 5.1.3(3) is excluded on the actual reselected omega-span. -/
theorem rankOne_local_cartan_not_natural_fixed_quotient_omega_span
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n m : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    ¬ Chapter6.Source.IsNaturalFixedQuotient L
      (Chapter6.Source.layer L
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)) m :=
  localCartan_not_natural_fixed_quotient_omega_span
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
