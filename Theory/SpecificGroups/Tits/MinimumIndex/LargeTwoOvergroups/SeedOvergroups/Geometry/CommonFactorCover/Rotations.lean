module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern00
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern01
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern02
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern03
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern04
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern05
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern06
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern07
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern08
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern10
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern11
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern12
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern13
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern14
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern15
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern16
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations.Pattern17

/-!
# Every rotated representative has an original common-factor representative

For each of the seventeen required place patterns, every published Sylow
representative followed by an allowed rotation is a listed common factor times
one of the original rows. Indexed row certificates and bounded three-point
checks establish all 21,632 matches. The factor list, row list, Sylow words,
and left multiplication convention are unchanged.

This is the unconditional rotation premise of
`Geometry.commonFactorCover_of_sylow_covers`. Exhaustiveness of the Sylow
representatives and closure of the factor list belong to its other inputs.
Source: Parrott (1972), §5, p.683; CommonFactorCover/source/README.md.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover

/-- Every allowed rotated Sylow representative is a factor times an original row. -/
theorem rotationFactorCover (t : Fin 18) (ht : t ≠ 9) :
    ∀ j ∈ placePattern t, ∀ k : Fin 32, ∀ e : Nat,
      e < rotationCount j → ∃ q ∈ factors t, ∃ r ∈ rows t,
        conjugate j (atlas1600SylowTwoNormalForm (sylowRepresentatives t j k) *
          rotation j ^ e) = q * rowElement r := by
  fin_cases t
  · exact Rotations.Pattern00.cover
  · exact Rotations.Pattern01.cover
  · exact Rotations.Pattern02.cover
  · exact Rotations.Pattern03.cover
  · exact Rotations.Pattern04.cover
  · exact Rotations.Pattern05.cover
  · exact Rotations.Pattern06.cover
  · exact Rotations.Pattern07.cover
  · exact Rotations.Pattern08.cover
  · exact (ht rfl).elim
  · exact Rotations.Pattern10.cover
  · exact Rotations.Pattern11.cover
  · exact Rotations.Pattern12.cover
  · exact Rotations.Pattern13.cover
  · exact Rotations.Pattern14.cover
  · exact Rotations.Pattern15.cover
  · exact Rotations.Pattern16.cover
  · exact Rotations.Pattern17.cover

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover
