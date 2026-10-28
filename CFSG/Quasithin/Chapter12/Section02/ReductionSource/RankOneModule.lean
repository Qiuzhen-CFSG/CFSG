module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModulePreparation
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleExceptional
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRestriction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleField

/-!
# Conditional assembly of the rank-one exit for the original Chapter 12 choice

The generic source exit retains the exceptional A₅ module case of 5.2.3.
If no outside subgroup has generation parameter greater than one, the
complementary recognition input excludes failure of the module conclusion.
Hypothesis 12.2.3 eliminates the actual global alternatives. Restricting the
resulting model of [R₂(LT),L] gives the original chosen module, and its
concrete quotient actor forces n = 2.

Both source exits remain explicit earlier inputs. In particular this does
not prove unmodified 6.2.20, its universal numerical clause, or the missing
5.2.3/6.2.19 source arguments. The assembly owner must discharge both exits.
Source: Aschbacher--Smith, pp.649,690--691,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The source exclusions concern the very same ambient group. -/
theorem Hypothesis1223.not_rankOne_globalExit
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ¬ RankOneModule.GlobalExit G := by
  rintro (⟨f, hf, hg⟩ | hg | hg)
  · exact h.no_rankTwo f hf hg
  · exact h.no_M22 hg
  · exact h.no_M23 hg

namespace ChosenModule
variable (D : ChosenModule T L V)
include D

/-- The two earlier source exits imply the model on the entire commutator
layer. The exceptional generic case is kept as a module case throughout. -/
theorem rankOne_layer_of_source_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hgeneric : RankOneModule.GenericExit T L)
    (hsmall : RankOneModule.SmallExit T L) :
    Chapter6.Source.IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L) := by
  classical
  have hout := D.rankOne_hasMaximalOutside_of_many h.toHypothesis1221 hmany
  by_cases hlarge : ∃ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H
  · obtain ⟨H, hH, hn⟩ := hlarge
    exact (hgeneric hout H hH hn).resolve_right h.not_rankOne_globalExit
  · by_contra hmodel
    apply h.no_M22
    apply hsmall hout _ hmodel
    intro H hH
    exact Nat.le_of_not_gt (fun hn => hlarge ⟨H, hH, hn⟩)

/-- The actual chosen Irr⁺ section is one A₅ module and the original binary
field exponent is two, conditional only on the two earlier source exits. -/
theorem rankOne_module_of_source_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hgeneric : RankOneModule.GenericConfigurationExit T L)
    (hsmall : RankOneModule.SmallExit T L) :
    n = 2 ∧ Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  have hmodel := D.a5_model_of_one_or_two_on_overgroup D.le_rankOne_commutatorLayer
    (D.rankOne_layer_of_source_exits_of_many h hmany
      (RankOneModule.genericExit_of_configuration hgeneric) hsmall)
  refine ⟨?_, hmodel⟩
  obtain ⟨e, _⟩ := hmodel
  exact Chapter6.Source.exponent_eq_two_of_psl_and_a5 hn hpsl e

end ChosenModule
end CFSG.Quasithin.Chapter12.Section02
