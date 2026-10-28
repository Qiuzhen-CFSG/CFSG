module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.RotationTest
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.SylowCover

/-!
# Common factors and coverage of the literal place unions

Every stored common factor belongs to every listed place, unconditionally.
For coverage, first enumerate the conjugated parabolic as a Sylow word times
a rotation. Split the Sylow word into a common factor times one of 32 words,
then match that word times the rotation with one of the original rows.

The finite certificates in SylowCover prove exhaustiveness of the factor list
in its generated subgroup and Sylow coset coverage. Rotations proves the matches
to the original rows. The final theorem discharges all three inputs for each
pattern other than 9, supplying the coverage premise of the place geometry.
Source: Parrott (1972), §5, p.683; the original place and seed JSON witnesses.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
open CommonFactorCover

/-- Two smaller finite covers imply coverage by the original literal rows.
The independent Sylow and rotation producers must discharge every premise. -/
theorem commonFactorCover_of_sylow_covers (t : Fin 18)
    (hfactors : ∀ q : Atlas1600Group, q ∈ factorSubgroup t → q ∈ factors t)
    (hsylow : ∀ j ∈ placePattern t, ∀ n : Fin 2048,
      ∃ q : Atlas1600Group, q ∈ factorSubgroup t ∧ ∃ k : Fin 32,
        conjugate j (atlas1600SylowTwoNormalForm n) =
          q * conjugate j (atlas1600SylowTwoNormalForm (sylowRepresentatives t j k)))
    (hrotation : ∀ j ∈ placePattern t, ∀ k : Fin 32, ∀ e : Nat,
      e < rotationCount j → ∃ q ∈ factors t, ∃ r ∈ rows t,
        conjugate j (atlas1600SylowTwoNormalForm (sylowRepresentatives t j k) *
          rotation j ^ e) = q * rowElement r)
    (x : Atlas1600Group) (hx : ∃ j ∈ placePattern t, x ∈ place j) :
    ∃ q ∈ factors t, ∃ r ∈ rows t, x = q * rowElement r := by
  obtain ⟨j, hj, hx⟩ := hx
  obtain ⟨n, e, he, rfl⟩ := place_normalForm_surjective j x hx
  obtain ⟨q, hq, k, hn⟩ := hsylow j hj n
  obtain ⟨q', hq', r, hr, hrot⟩ := hrotation j hj k e he
  refine ⟨q * q', hfactors _ ((factorSubgroup t).mul_mem hq
    (factors_mem_factorSubgroup t q' hq')), r, hr, ?_⟩
  rw [conjugate_mul, hn, mul_assoc, ← conjugate_mul, hrot, mul_assoc]

/-- Every element of the literal place union is a listed common factor times
an original representative. This discharges the coverage premise of
`placePattern_geometry_of_representative_certificates` for every required pattern. -/
theorem commonFactorCover (t : Fin 18) (ht : t ≠ 9)
    (x : Atlas1600Group) (hx : ∃ j ∈ placePattern t, x ∈ place j) :
    ∃ q ∈ factors t, ∃ r ∈ rows t, x = q * rowElement r :=
  commonFactorCover_of_sylow_covers t (factorSubgroup_mem_factors t ht)
    (sylowFactorCover t ht) (rotationFactorCover t ht) x hx

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
