module

public import Theory.GroupTheory.MinimalSimple
public import Theory.SpecificGroups.Tits.AtlasRepresentation
public import Theory.SpecificGroups.Tits.AtlasWitness

/-!
# Parrott's presented group is not minimal simple

The ATLAS permutations contain an explicitly certified proper nonsolvable
subgroup, constructed in `AtlasWitness`. The verified homomorphism from
Parrott's presentation in `AtlasRepresentation` has both ATLAS generators in
its image, so that witness pulls back to a proper nonsolvable subgroup.
Thus no finite minimal simple group can be isomorphic to the presentation.

The representation need not be faithful. No finiteness assumption on the
presented group is used: all finiteness assumptions belong to the candidate
minimal simple group. The only model interface is the proved existence of a
homomorphism whose range contains `atlasA` and `atlasB`. All relators and
permutation certificates are checked in Lean; neither presentation faithfulness
nor a global recognition theorem is needed.

Sources: Parrott (1972), §5, p. 683, and the ATLAS permutation data recorded
in `refs/original/n-group-global/`.
-/

namespace Tits

/-- A minimal simple group has no representation whose range contains both
ATLAS generators: their image contains the proper nonsolvable witness. -/
public theorem not_minimalSimple_of_atlas_range {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 1600))
    (ha : atlasA ∈ f.range) (hb : atlasB ∈ f.range) : ¬ IsMinimalSimple G := by
  intro hG
  exact not_isSolvable_atlasWitness
    (hG.isSolvable_of_lt_range f atlasWitness (atlasWitness_lt ha hb))

/-- A representation of Parrott's presentation containing the ATLAS generators
excludes every minimal-simple isomorphism, without requiring faithfulness. -/
public theorem not_mulEquiv_parrottGroup_of_atlas_range
    (f : ParrottGroup →* Equiv.Perm (Fin 1600))
    (ha : atlasA ∈ f.range) (hb : atlasB ∈ f.range)
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (e : G ≃* ParrottGroup) : False := by
  apply not_minimalSimple_of_atlas_range (f.comp e.toMonoidHom) ?_ ?_ hG
  · obtain ⟨x, hx⟩ := ha
    exact ⟨e.symm x, by simpa using hx⟩
  · obtain ⟨x, hx⟩ := hb
    exact ⟨e.symm x, by simpa using hx⟩

/-- No finite minimal simple group is isomorphic to Parrott's presented group.
The proper nonsolvable subgroup is pulled back from the verified ATLAS image;
no global finiteness instance for the presentation is assumed. -/
public theorem not_mulEquiv_parrottGroup
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (e : G ≃* ParrottGroup) : False := by
  obtain ⟨f, ha, hb⟩ := exists_parrott_atlas_representation
  exact not_mulEquiv_parrottGroup_of_atlas_range f ha hb hG e

end Tits
