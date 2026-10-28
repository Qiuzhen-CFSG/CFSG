module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.ExceptionalGeneration.Checks

/-!
# Candidate-derived containment for every exceptional thirteen-pair

For each of the 27 fixed exceptional representatives, two checked recovery
words put generators of a subgroup containing a literal candidate derived
subgroup into a conjugate of the actual pair subgroup. The witness is an
actual word in the standard ATLAS generators. All finite equalities are
checked on the independently certified three-point permutation base.

This discharges precisely the exceptional-case input to
`PairGeneration.generation_of_three_certificates`; neither whole-group
recovery outside the exceptional list nor double-coset coverage is assumed.
Source: the primary ATLAS Tits programs and attribution documented in
`ExceptionalGeneration/source/README.md`.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration

/-- Every exceptional thirteen-pair contains a conjugate of one of the literal
max1, max2 or max4 ambient derived subgroups. -/
public theorem exceptional_generation (k : Fin 3010) (hk : k ∈ exceptionalIndices) :
    ∃ (i : Fin 3) (g : Atlas1600Group),
      candidateDerived i ≤ (pairSubgroup (representative k)).map
        (MulAut.conj g).toMonoidHom := by
  obtain ⟨i, g, wa, wb, ha, hb⟩ := ExceptionalGeneration.exceptional_recoveries k hk
  exact ⟨i, standardWord g,
    ExceptionalGeneration.derived_le_map_of_recovery k g i wa wb ha hb⟩

end Tits.MinimumIndexThirteen.PairGeneration
