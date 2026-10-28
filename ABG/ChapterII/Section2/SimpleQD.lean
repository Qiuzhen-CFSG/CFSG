module

public import ABG.Basic
public import ABG.ChapterII.Section1.FusionFrame
public import ABG.ChapterII.Section2.QuasiQDCharacterization

/-!
# Simple groups with quasi-dihedral Sylow subgroups are QD-groups

For a finite simple group with a quasi-dihedral Sylow two-subgroup, this
module supplies the full QD-group predicate of ABG Chapter II, Section 2,
Definition 1. This places the groups in the three main theorems within the
local classes used to construct their characteristic power.

Choose actual four and quaternion subgroups inside the given Sylow subgroup
using the frame-existence theorem. The simple-group corollary of the full
fusion proposition excludes each alternative with a normal subgroup of
index two and provides every clause of the QD fusion pattern.

Source: `refs/latex/alperin-brauer-gorenstein.tex`, Chapter II, Section 1,
Proposition 1 and Section 2, Definition 1, article pages 10-14.
-/

namespace ABG

/-- A finite simple group with quasi-dihedral Sylow two-subgroups is a QD-group. -/
public theorem isQDGroup_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hS : HasQuasiDihedralSylowTwoSubgroups G) : IsQDGroup G := by
  obtain ⟨S, hS⟩ := hS
  obtain ⟨T, Q, hframe⟩ := exists_quasiDihedralFusionFrame S hS
  exact Or.inl ⟨S, T, Q, hframe, quasiDihedral_qdPattern_of_simple S T Q hframe⟩

end ABG
