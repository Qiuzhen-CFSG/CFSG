module

public import Theory.SpecificGroups.PSL3Three.MaximalClassification
public import Theory.SpecificGroups.PSL3Three.ParabolicSolvability
public import Theory.SpecificGroups.PSL3Three.MonomialSolvability
public import Theory.SpecificGroups.PSL3Three.SingerNormalizerSolvability
public import Theory.GroupTheory.SolvableConjugate

/-!
# Solvable maximal subgroups of PSL₃(3)

This module combines the exact conjugacy classification with solvability of
the four concrete candidates: the line and plane stabilizers, the monomial
subgroup, and the Singer normalizer. Solvability transports by conjugation,
so every maximal proper subgroup is solvable.

The re-exported `isCoatom_iff_conjugate` and
`proper_subgroup_le_conjugate_PSL` certify equality and containment of actual
matrix subgroups. Their finite completeness certificate is checked in Lean;
solvability of each candidate is proved independently of that classification.

Source: GLS III, Theorem 6.5.3(a–c), in `refs/KGroup/GLS3/chapter6.tex`.
See `MaximalClassification` for the necessary proper-subgroup restriction
and the distinction between abstract isomorphism and concrete conjugacy.
-/

namespace Matrix.PSL3Three

/-- Every maximal proper subgroup of PSL₃(3) is solvable. -/
public theorem maximal_isSolvable (M : Subgroup PSL) (hM : IsCoatom M) :
    Group.IsSolvable M := by
  let := lineStabilizer_isSolvable
  let := planeStabilizer_isSolvable
  let := monomial_isSolvable
  let := singerNormalizer_isSolvable
  obtain ⟨g, h | h | h | h⟩ := (isCoatom_iff_conjugate M).mp hM
  · exact Group.isSolvable_of_le_conjugate M lineStabilizer g h.le
  · exact Group.isSolvable_of_le_conjugate M planeStabilizer g h.le
  · exact Group.isSolvable_of_le_conjugate M monomial g h.le
  · exact Group.isSolvable_of_le_conjugate M singerNormalizer g h.le

end Matrix.PSL3Three
