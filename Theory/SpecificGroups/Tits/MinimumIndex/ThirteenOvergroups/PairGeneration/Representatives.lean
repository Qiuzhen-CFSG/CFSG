module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Codes
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Words

/-!
# Actual group elements for the fixed thirteen-pair candidates

Every candidate is a word in the actual ATLAS standard generators. In particular,
its ambient membership requires no finite check or group-family identification.
Coverage by their normalizer double cosets and generation for the nonnormalizing
representatives are separate remaining certificate obligations.

Source: the primary ATLAS Tits generators; see `source/README.md`.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration

/-- The fixed representative family used by both finite certificate obligations. -/
@[expose] public def representative (k : Fin 3010) : Atlas1600Group :=
  standardWord (representativeCode k)

/-- Candidate exceptional indices, from untrusted discovery. Membership in this list
makes no assertion about subgroup order or generation. Both parts of the resulting
finite split require independent Lean proofs. -/
@[expose] public def exceptionalIndices : List (Fin 3010) :=
  [1, 2, 3, 4, 5, 18, 56, 239, 520, 715, 726, 937, 1003, 1022, 1441, 1449, 1633, 1877, 1879, 1997, 2218, 2405, 2562, 2662, 2701, 2733, 2935]

/-- The distinguished identity representative belongs to the actual normalizer. -/
public theorem representative_zero_mem : representative 0 ∈ thirteenNormalizer := by
  change (1 : Atlas1600Group) ∈ thirteenNormalizer
  exact thirteenNormalizer.one_mem

end Tits.MinimumIndexThirteen.PairGeneration
