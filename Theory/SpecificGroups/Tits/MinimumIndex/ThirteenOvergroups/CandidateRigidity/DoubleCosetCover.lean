module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.DoubleCosetCover.Packed
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.DoubleCosetCover.Checks0
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.DoubleCosetCover.Checks1

/-!
# The two six-double-coset covers by the literal candidate cores

For each core, 3200 marked representatives have the form r*w, where r is one
of the six published words and w is a core word. Kernel-checked transitions
under the standard generators give an exhaustive cover by word induction.
The packed point maps are connected to the actual ATLAS words, and the
three-point base upgrades every checked transition to a group equality.

Source: the original ATLAS max1 and max2 programs and attribution in
`MinimumIndex/source/`; discovery witnesses and conventions are preserved in
`DoubleCosetCover/source/`. Neither a core order nor a derived-subgroup
identification is required. This supplies the cover premise of
`candidateDerived_rigid_firstTwo_of_cover` in the separately owned assembly.
-/

namespace Tits.MinimumIndexThirteen.CandidateRigidity

/-- Every actual Atlas element belongs to one of the six literal double cosets
of either commutator-generated candidate core. -/
public theorem core_doubleCoset_cover (i : Fin 2) (x : Atlas1600Group) :
    ∃ (a b : core (i.castLE (by decide))) (j : Fin 6),
      x = a.val * representative i j * b.val := by
  fin_cases i
  · exact CoreCover.cover_of_blocks 0 (CoreCover.coreMap 0) (CoreCover.coreMap_eq 0)
      CoreCover.table0 CoreCover.table0_zero CoreCover.blocks0 x
  · exact CoreCover.cover_of_blocks 1 (CoreCover.coreMap 1) (CoreCover.coreMap_eq 1)
      CoreCover.table1 CoreCover.table1_zero CoreCover.blocks1 x

end Tits.MinimumIndexThirteen.CandidateRigidity
