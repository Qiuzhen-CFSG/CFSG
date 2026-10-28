module

public import Theory.SpecificGroups.LieType.ParabolicModelVersions
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData

/-!
# Root candidates for the Ree F₄ model

The candidate uses the actual fixed root subgroups in `ReeF4.Model m`.  The
radical is the root-defined subgroup, while the complementary seed and torus
remain part of the full parabolic.  At `m = 0` this still describes the full
fixed group; the derived Tits endpoint is supplied separately by
`ReeF4.DerivedTits`.
-/

@[expose] public section

namespace Theory.SpecificGroups.LieType.ParabolicModelVersions

open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds

/-- The fixed-root Borel, marked parabolic and radical candidate. -/
noncomputable def reeF4RootCandidate (m : ℕ) (s : Side) :
    Candidate (ReeF4.Model m) where
  borel := borel m
  parabolic := parabolic m s
  radical := radical m s
  borel_le_parabolic := borel_le_parabolic m s
  radical_le_parabolic :=
    (radical_le_unipotent m s).trans
      ((unipotent_le_seed m s).trans (seed_le_parabolic m s))

@[simp] theorem reeF4RootCandidate_borel (m : ℕ) (s : Side) :
    (reeF4RootCandidate m s).borel = borel m := rfl

@[simp] theorem reeF4RootCandidate_parabolic (m : ℕ) (s : Side) :
    (reeF4RootCandidate m s).parabolic = parabolic m s := rfl

@[simp] theorem reeF4RootCandidate_radical (m : ℕ) (s : Side) :
    (reeF4RootCandidate m s).radical = radical m s := rfl

end Theory.SpecificGroups.LieType.ParabolicModelVersions

end
