module
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Native
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.Opposition

/-!
# The native Ree linear parabolic has trivial normal core

The linear radical is normal and self-centralizing in its full parabolic.
Its disjointness from the opposite parabolic therefore kills the normal core.
This supplies the native input for faithfulness of full-extension completions,
without assuming simplicity or a group identification.
Source: GLS3 Theorem 2.6.5 and Aschbacher–Smith F.4.3–6.
-/

public noncomputable section
namespace ReeF4.SmallCompletion
open Subgroup Parabolics

/-- The actual linear parabolic has trivial normal core for every m>0. -/
theorem linear_normalCore_eq_bot (m : ℕ) (hm : 0 < m) :
    (parabolic m .linear).normalCore = ⊥ :=
  SectionGeometry.parabolic_normalCore_eq_bot_of_radical m .linear
    (SectionGeometry.LinearRadical.parabolic_le_radical_normalizer m .linear)
    (SectionGeometry.LinearRadical.centralizer_le_radical m hm)
    (SectionGeometry.Opposition.exists_linear_opposition m)

end ReeF4.SmallCompletion
