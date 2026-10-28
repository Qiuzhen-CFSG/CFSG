module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Natural.Exclusion

/-!
# Excluding the original binary-three constrained branch

Local recognition gives an actual natural three-space or natural–dual pair
on [D.moduleSubgroup,L]. The pair is excluded by the inner/outer point-action
contradiction, and the natural space by the smaller-orbit parabolic endgame.
This closes the binary quotient branch for every size of the full moved
module. The remaining Suzuki alternative is only an actual quotient; its
representation and exclusion are not assumed here.

The Source assembly applies this reduction to ConstrainedExclusionAt and
the literal point-control consumer. Source: Aschbacher–Smith 10.2.9,
printed pp.751–753, without 10.2.7 or the later generation bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The full original binary-three branch is impossible. The local
recognition supplies a natural or natural–dual marking; both have now been
excluded using their actual containing actions and the local parabolic endgame. -/
theorem Context.no_original_binary_three (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) : False := by
  obtain ⟨f,h | h⟩ := c.local_binary_natural_or_pair e
  · exact c.no_localNaturalCover ⟨f,h⟩
  · exact c.no_local_naturalDual f h.some

/-- An original constrained context can only have a genuine Suzuki quotient.
This is a quotient statement; no Suzuki representation is asserted. -/
theorem Context.original_suzuki_quotient (c : Context D t v I) :
    ∃ m : ℕ, 0 < m ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rcases c.original_local_natural_or_suzuki with h | h
  · exact (c.no_localNaturalCover h).elim
  · exact h

end CFSG.Quasithin.Chapter10.PointControl.Constrained
