module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalHermitian
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalMinusInversion

/-!
# The Hermitian Cartan branch on the original omega-span

The original witness gives a noncentral reduced omega-span at the same
Sylow choice and field degree. A genuine Hermitian model on that span
forces odd half-degree, centralization of the minus torus, and then degree
two. The existing recognition applies to the whole original module and
recovers the chosen A₅ marking, including its actual action.

Only the Hermitian model is explicit in this branch; no minus-torus or
parity premise remains. Producing the exhaustive source module alternatives
and the initial component-and-cubic witness still belongs to the universal
local Cartan source proof.
Source: Aschbacher--Smith 5.1.13, final paragraph, printed p.638,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Representation.OrthogonalFourMinus
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C : Subgroup G}
  (D : ChosenModule T L V)
include D
local instance (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))

/-- The actual omega-span can be reselected under the original source input. -/
theorem rankOne_local_cartan_omega_span_input
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    Input KnownSimple.IsKnownSimple T L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n :=
  localCartan_omega_span_input
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d

/-- The actual Hermitian omega-span gives degree two, the whole exceptional
conclusion and the original chosen module, with torus geometry discharged. -/
theorem rankOne_local_cartan_escape_of_hermitian_omega_span
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (s : ℕ) [NeZero s]
    (hm : Chapter6.Source.IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (Representation.SL2.BinarySmall.hermitian s)) :
    n = 2 ∧ CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  obtain ⟨he,hout⟩ := localCartan_escape_of_hermitian_omega_span
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d s hm
  have hx := RankOneModule.exceptional_of_cartan_conclusion hout
  exact ⟨he,hout,hx,(D.rankOne_exceptional_module_and_exponent hn hpsl hx).2⟩

/-- At larger original degrees the orthogonal source row is excluded. -/
theorem rankOne_local_cartan_not_hermitian_omega_span
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 2 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (s : ℕ) [NeZero s] :
    ¬ Chapter6.Source.IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (Representation.SL2.BinarySmall.hermitian s) :=
  localCartan_not_hermitian_omega_span
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by omega) hpsl)
    hH hgen c hY d hn s

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
