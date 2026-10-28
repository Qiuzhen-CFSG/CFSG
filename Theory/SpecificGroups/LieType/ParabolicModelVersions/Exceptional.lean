module

public import Theory.SpecificGroups.LieType.ParabolicModelVersions
public import Theory.SpecificGroups.LieType.ExceptionalSplitParabolics

/-!
# Root candidates for the split exceptional models

The candidate below is built from the literal central-quotient root groups and
the coroot torus.  It is deliberately parameterised by a root pairing, so the
same comparison lemma applies to F₄, E₆, E₇ and E₈ without identifying an
elementary group with a full rational point group.
-/

@[expose] public section

namespace Theory.SpecificGroups.LieType.ParabolicModelVersions

open ExceptionalSplit ExceptionalSplit.Parabolics

variable {ι R M N F : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [CharP F 2]
  [P.IsRootSystem]

/-- The root-generated Borel, maximal parabolic and radical candidate in the
actual split exceptional central quotient. -/
noncomputable def exceptionalRootCandidate (j : b.support) :
    Candidate (ExceptionalSplit.Model P b F) where
  borel := positive P b F ⊔ torus P b F
  parabolic := maximal P b F j
  radical := radical P b F j
  borel_le_parabolic := le_sup_left
  radical_le_parabolic := radical_le_maximal P b F j

@[simp] theorem exceptionalRootCandidate_borel (j : b.support) :
    (exceptionalRootCandidate (P := P) (b := b) (F := F) j).borel =
      positive P b F ⊔ torus P b F := rfl

@[simp] theorem exceptionalRootCandidate_parabolic (j : b.support) :
    (exceptionalRootCandidate (P := P) (b := b) (F := F) j).parabolic =
      maximal P b F j := rfl

@[simp] theorem exceptionalRootCandidate_radical (j : b.support) :
    (exceptionalRootCandidate (P := P) (b := b) (F := F) j).radical =
      radical P b F j := rfl

end Theory.SpecificGroups.LieType.ParabolicModelVersions

end
