module

public import Theory.SpecificGroups.LieType.ParabolicModelVersions
public import Theory.SpecificGroups.Triality.RootParabolics

/-!
# Root candidates for the genuine triality carrier

The carrier here is `Triality.Standard.Carrier`, the elementary fixed subgroup
of the split D₄ graph-field model modulo its actual centre.  The candidate
radical is the descended positive root subgroup.  The definitions are kept
separate from the auxiliary three-coordinate matrix model.
-/

@[expose] public section

namespace Theory.SpecificGroups.LieType.ParabolicModelVersions

open Triality.Standard Triality.Standard.Parabolics

/-- The Borel, marked parabolic and positive-root candidate in the genuine
graph-field carrier. -/
noncomputable def trialityRootCandidate (P : Parameters) (a : Node) :
    Candidate (Triality.Standard.Carrier P) where
  borel := borel P
  parabolic := parabolic P a
  radical := unipotent P
  borel_le_parabolic := borel_le_parabolic P a
  radical_le_parabolic :=
    (unipotent_le_borel P).trans (borel_le_parabolic P a)

@[simp] theorem trialityRootCandidate_borel (P : Parameters) (a : Node) :
    (trialityRootCandidate P a).borel = borel P := rfl

@[simp] theorem trialityRootCandidate_parabolic (P : Parameters) (a : Node) :
    (trialityRootCandidate P a).parabolic = parabolic P a := rfl

@[simp] theorem trialityRootCandidate_radical (P : Parameters) (a : Node) :
    (trialityRootCandidate P a).radical = unipotent P := rfl

end Theory.SpecificGroups.LieType.ParabolicModelVersions

end
