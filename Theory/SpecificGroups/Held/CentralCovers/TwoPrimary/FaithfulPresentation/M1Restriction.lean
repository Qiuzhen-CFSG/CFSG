module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.SourceRelations

/-!
# A finite-presentation route to faithfulness on M₁

If the twelve candidate relators hold on the three abstract M₁ generators,
the auxiliary presentation surjects onto M₁. A finite bound of 1,958,400 for
that presentation then bounds M₁. An independent lower bound of 1,958,400
for the concrete image makes the surjection from M₁ onto its image bijective.

All three missing inputs remain explicit. This module does not yet prove
unconditional injectivity of `m1Map`. It uses neither a global coset cover,
finiteness of the Held presentation, nor multiplier information.

Source: the literal M₁ in John Bray's `Held/Model/Source/HeG1-P1.M`;
candidate local presentation data and provenance are in `M1Restriction/source/`.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open Subgroup.CosetWordCertificate

/-- The candidate presentation maps to the original group only after its
relations have been derived there. -/
def localHom (hrels : LiftedRelations) : LocalPresentation →* Presentation :=
  PresentedGroup.toGroup (f := liftedGenerator) (by
    rintro _ ⟨i, rfl⟩
    exact hrels i)

theorem localHom_range (hrels : LiftedRelations) : (localHom hrels).range = m1 := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    (Set.range localRelator), MonoidHom.map_closure, ← Set.range_comp,
    m1_eq_closure_range]
  congr 1
  apply congrArg Set.range
  funext i
  exact PresentedGroup.toGroup.of _

/-- All required finiteness is derived from the finite auxiliary presentation. -/
theorem m1_bound (hrels : LiftedRelations) (hbound : LocalPresentationBound) :
    Finite m1 ∧ Nat.card m1 ≤ 1958400 := by
  let := hbound.1
  let f := localHom hrels
  have hfinite : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hcard : Nat.card f.range ≤ 1958400 :=
    (Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective).trans hbound.2
  have hr : f.range = m1 := localHom_range hrels
  exact hr ▸ ⟨hfinite, hcard⟩

/-- Conditional local assembly. Its three independent certificate premises
must all be discharged before claiming faithfulness on the source M₁. -/
theorem m1Map_injective_of_certificates (hrels : LiftedRelations)
    (hbound : LocalPresentationBound) (hlower : ConcreteLowerBound) :
    Function.Injective m1Map := by
  obtain ⟨hfinite, hcard⟩ := m1_bound hrels hbound
  let := hfinite
  have hrange : Nat.card m1 ≤ Nat.card m1Map.range := by
    rw [m1Map_range]
    exact hcard.trans hlower
  have hi := (m1Map.rangeRestrict_surjective.bijective_of_nat_card_le hrange).1
  intro g h hgh
  exact hi (Subtype.ext hgh)

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
