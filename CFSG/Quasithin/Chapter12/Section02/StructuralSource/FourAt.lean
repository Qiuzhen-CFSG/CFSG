module
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.FourSourceAt
import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalSourceComplete

/-!
# Structural 12.2.2 after the original doubled-natural exclusion

The proved original A5 tensor exclusion supplies that normalization branch;
only the nonnormal survivor remains. Normalization selects an actual chosen
module. The original rank-one exits and completed Mathieu source give FF on its whole orbit.
The now completed degree-four/five doubled-natural exclusion eliminates
the moved alternative, yielding invariance, reducedness and TI directly.
This structural producer requires no nonbinary-natural module classification;
that independent duty remains only in the seven-module conclusion.
The tensor proof is an implementation import: its public input predicate is
already available, and no private implementation name enters this interface.
Source: Aschbacher--Smith 12.1.11 and 12.2.2, printed pp.794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
variable
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hdoubled : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hgeneric : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      RankOneModule.GenericConfigurationExit T L)
    (hsmall : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      RankOneModule.SmallExit T L)

include hmany hreduction hdoubled hgeneric hsmall

/-- Original structure uses the completed doubled-natural source without
assuming the independent seven-module classification. -/
theorem structural1222At_after_original_four_of_many :
    Structural1222At KnownSimple.IsKnownSimple T := by
  have htensor := Chapter10.sourceA5TensorExclusionAt_from_source T
  intro L h
  have hn := sourceNormalization1222At_after_replacement_of_many
    hmany htensor hreduction L h
  obtain ⟨U,hU⟩ := h.toHypothesis1221.exists_chosen_of_normalizes hn
  refine ⟨hn,⟨⟨U,hU⟩⟩,?_⟩
  intro V D
  have hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
    intro n hn hpsl
    exact (D.rankOne_module_of_source_exits_of_many h hmany hn hpsl
      (hgeneric L V h D n hn hpsl) (hsmall L V h D n hn hpsl)).2
  have hf := D.sourceOrbit_ff_of_normalized_inputs_of_many h hmany
    (hdoubled L V h D) (fun hV _ hm hnon =>
      (D.sourceOrbit_m22_code_excluded_of_many h hmany hV hnon
        (D.sourceOrbit_mathieu_remaining_m22_code_of_many h hmany hV hnon hm)).elim) hrank
  exact D.structural_of_not_doubled_of_many h hmany
    (D.not_markedDoubled_of_orbit_source_inputs h (Or.inl hf) hrank
      (fun _ B => D.doubleNatural_excluded_of_many h hmany B))

end CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
