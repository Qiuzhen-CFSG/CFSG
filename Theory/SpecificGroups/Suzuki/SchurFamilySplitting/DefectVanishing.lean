module

public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.DefectVanishing.ScalarStem
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.LocalCover

/-!
# The conditional ordinary Suzuki Schur-kernel calculation

Apply scalar-invariant central-defect vanishing to `Family.canonicalRootData`,
the literal root preimage in the canonical universal cover. The existing
local-to-global kernel comparison then kills the full Schur kernel.

Only the two finite-field vanishing predicates remain explicit. In particular,
no section, lift, class-two hypothesis or multiplier bound is assumed. The
field calculation and subsequent construction of a splitting are separate
steps; the exceptional parameter `m = 1` is excluded by the triple-map input,
not by any alteration of the covering data.

Source: Aschbacher--Smith I.1.1--I.1.3, printed p.407/PDF p.418 of
`refs/quasithin.pdf`; GLS3 §6.1 and standard central commutator calculus.
-/

namespace BenderSuzuki.MatrixGroups.SchurCover.Family

/-- The actual canonical Suzuki Schur kernel vanishes when scalar-invariant
pairings and triple maps on its defining field vanish. -/
public theorem canonicalKernel_eq_bot_of_invariants (m : ℕ) [Fact (0 < m)]
    (h₂ : ScalarInvariantMaps.PairingsVanish.{0,0} (Field m))
    (h₃ : ScalarInvariantMaps.TriplesVanish.{0,0} (Field m)) : Kernel m = ⊥ :=
  canonicalKernel_eq_bot_of_local m
    ((canonicalRootData m).kernel_eq_bot_of_invariants h₂ h₃)

end BenderSuzuki.MatrixGroups.SchurCover.Family
