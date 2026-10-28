module
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups

/-!
# The normalizer of the binary point parabolic

The standard point parabolic in SL₃(2) is self-normalizing. It is maximal,
and conjugating an upper transvection by the adjacent reflection leaves
the parabolic, so the parabolic is not normal. This supplies the precise
self-normalization input for the regular-wreath maximality argument.

Source: the binary projective-plane geometry in Aschbacher--Smith I.5.4,
p.420; used in the paired parabolic of 10.2.4, p.747.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two

/-- The standard point parabolic equals its normalizer in the actual matrix group. -/
theorem pointParabolicSL_normalizer :
    normalizer (pointParabolicSL : Set SL) = pointParabolicSL := by
  have hnot : ¬ pointParabolicSL.Normal := by
    intro hn
    have hp : Bruhat.upper 1 ∈ pointParabolicSL := (Bruhat.upper_mem 1).1
    have hc := hn.conj_mem (Bruhat.upper 1) hp (Bruhat.perm 2)
    have hne : Bruhat.perm 2 * Bruhat.upper 1 * (Bruhat.perm 2)⁻¹ ∉ pointParabolicSL := by
      rw [mem_pointParabolicSL_iff]
      decide
    exact hne hc
  apply le_antisymm _ pointParabolicSL.le_normalizer
  by_contra hn
  have he := isCoatom_pointParabolicSL.2 _
    (lt_of_le_not_ge pointParabolicSL.le_normalizer hn)
  exact hnot (normalizer_eq_top_iff.mp he)

end Matrix.PSL3Two
