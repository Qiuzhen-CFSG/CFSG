module

public import Theory.SpecificGroups.G2Five.AtlasBoundSubgroup
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Transferring a local presentation bound to the ATLAS word subgroup

A presentation on the two explicit subgroup words maps onto `boundSubgroup`
provided each of its relators follows from the retained 22 ambient relators.
Consequently a finite cardinal bound for that local presentation bounds the
actual subgroup. The permutation image in `AtlasBoundSource/Verify.g` is only
a source of candidate local relators; it does not supply either proof premise.

The containing-image variant also permits a presentation with additional
generators: it suffices to express both fixed words in its image. This supports
Schreier generators without having to eliminate them down to the fixed pair.

Source: the ATLAS words in `AtlasBoundSubgroup` and the quotient property of
presented groups.
-/

namespace G2Five.AtlasPresentation

/-- A finite group whose image contains both fixed words bounds their subgroup.
The image may be larger than the subgroup, and its generators need not be the
two fixed words. -/
public theorem finite_card_boundSubgroup_le_of_covering_hom
    {L : Type*} [Group L] (f : L →* Model)
    (hwords : ∀ b, boundGenerator b ∈ f.range)
    (hbound : Finite L ∧ Nat.card L ≤ 1500000) :
    Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 1500000 := by
  let := hbound.1
  have hle : boundSubgroup ≤ f.range := by
    rw [boundSubgroup, Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact hwords b
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hinj := Subgroup.inclusion_injective hle
  refine ⟨Finite.of_injective (Subgroup.inclusion hle) hinj, ?_⟩
  exact (Nat.card_le_card_of_injective _ hinj).trans
    ((Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective).trans hbound.2)

/-- A local presentation whose two canonical generators map to the two fixed
words, once its relations have been proved in the ambient presentation. -/
@[expose] public def boundLocalHom (rels : Set (FreeGroup Bool))
    (hrels : ∀ r ∈ rels, FreeGroup.lift boundGenerator r = 1) :
    PresentedGroup rels →* Model :=
  PresentedGroup.toGroup hrels

/-- The local presentation maps onto precisely the specified word subgroup. -/
public theorem boundLocalHom_range (rels : Set (FreeGroup Bool))
    (hrels : ∀ r ∈ rels, FreeGroup.lift boundGenerator r = 1) :
    (boundLocalHom rels hrels).range = boundSubgroup := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of rels,
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext b
  exact PresentedGroup.toGroup.of _

/-- A proved finite local presentation bounds the abstract word subgroup. -/
public theorem finite_card_boundSubgroup_le_of_presentation
    (rels : Set (FreeGroup Bool))
    (hrels : ∀ r ∈ rels, FreeGroup.lift boundGenerator r = 1)
    (hbound : Finite (PresentedGroup rels) ∧
      Nat.card (PresentedGroup rels) ≤ 1500000) :
    Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 1500000 := by
  let := hbound.1
  let f := boundLocalHom rels hrels
  have hfinite : Finite f.range :=
    Finite.of_surjective _ f.rangeRestrict_surjective
  have hcard : Nat.card f.range ≤ 1500000 :=
    (Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective).trans hbound.2
  exact (boundLocalHom_range rels hrels) ▸ ⟨hfinite, hcard⟩

end G2Five.AtlasPresentation
