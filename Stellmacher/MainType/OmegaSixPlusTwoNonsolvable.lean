module

public import Stellmacher.MainType.NineOne
public import Theory.SpecificGroups.PSL3Two.NonSolvable

/-!
# A nonsolvable two-local in the Omega-six-plus-two local type

The source-local configuration (9.1) includes a subgroup of order eight
whose full ambient normalizer has quotient PSL3(2). The subgroup is a
nontrivial two-group by its order, so its normalizer is two-local. The
surjective map onto the proved nonsolvable PSL3(2) excludes solvability of
that actual normalizer. No assumption on other ambient local subgroups or
recognition of an ambient named group is used.

Source: Stellmacher, Journal of Algebra 190 (1997), Theorem 1's final
assertion and the definition following (9.1), printed p.48.
-/

namespace Stellmacher

universe u

public theorem exists_nonsolvable_twoLocal_of_omegaSixPlusTwo_type
    {H : Type u} [Group H] [Finite H] (htype : IsOfOmegaSixPlusTwoType H) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  obtain ⟨data⟩ := htype
  let _ := data.groupK
  let _ := data.finiteK
  obtain ⟨U, _, hcard, hquotient⟩ := data.caseData.normalizer_witness
  have htwo : IsPGroup 2 U := IsPGroup.of_card (n := 3) hcard
  have hne : U ≠ ⊥ := by
    intro hbot
    simp only [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  refine ⟨Subgroup.normalizer (U : Set H), ⟨U, hne, htwo, rfl⟩, ?_⟩
  intro hsolvable
  let _ := hsolvable
  obtain ⟨projection, hsurjective, _⟩ := hquotient
  exact not_isSolvable_psl3_two (Group.isSolvable_of_surjective hsurjective)

end Stellmacher
