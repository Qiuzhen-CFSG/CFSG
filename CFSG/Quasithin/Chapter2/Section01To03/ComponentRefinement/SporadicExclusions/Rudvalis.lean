module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.SubnormalBlocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.CentralizerGeometry

/-!
# The Rudvalis branch of the local block exclusion

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS3 Table 5.3r and
its max4 justification, printed pp.291–292.

The max4 conjugate over the actual component Sylow, together with the original
involution centralizer, generates the degree-4060 Rudvalis quotient. Its full
preimage adjoined with S lies in L ∨ S and has a nontrivial self-centralizing
two-core, retaining the central two-kernel and possible component permutations.

`Rudvalis.CentralizerGeometry` constructs this local and its relative factor
series, whose factors are two-groups or simple groups of order 168.
`Rudvalis.SubnormalBlocks` excludes the allowed subnormal chi-zero blocks
using their intrinsic two-core quotients. The theorem below supplies the
resulting cover from the source setup and literal quotient/action alone.
The parent sporadic-exclusion module retains the final contradiction and
seven-case assembly.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase

/-- The Rudvalis local block cover required by 2.3.9(7), with its concrete
local geometry, central-cover transport and subnormal-block exclusion supplied. -/
theorem nonempty_centralizerBlockCover
    {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .ru) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) :=
  CentralizerGeometry.nonempty_centralizerBlockCover h d

end CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase
