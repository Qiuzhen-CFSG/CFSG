module

public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.MarkingConjugacy
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry

/-!
# Discharging the marking-conjugacy premise in the M₁₀ local geometry

Simultaneous conjugacy now supplies the alignment required by the existing
local-facts construction. Its extension-normality and full-normalizer upper
bound remain explicit: they belong to the independent action and normalizer
calculations. Thus this application removes precisely the marking premise in
Aschbacher's 4.9–4.10 local construction (2003, pp.41–42).
-/

@[expose] public section

namespace AlternatingSix.M10.LocalGeometry
open Subgroup ShadowLocal

/-- All marked local clauses follow from extension normality and the standard
normalizer upper bound, with simultaneous marking conjugacy discharged. -/
theorem nonempty_localFacts_of_normalizer (m : Marking) (hn : extension.Normal)
    (hN : normalizer (nine standardNine : Set AutA6) ≤
      nine standardNine ⊔ standardComplement) : Nonempty (LocalFacts m) :=
  nonempty_localFacts_of_normalizer_and_alignment m hn hN (nonempty_permutationAlignment m)

end AlternatingSix.M10.LocalGeometry
