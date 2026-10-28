module
public import Theory.Representation.HexacodeAction.FaithfulDegrees
public import Theory.Representation.HexacodeAction.CentralCharacter
public import Theory.GroupTheory.NoncentralChiefRefinement.ScalarCoordinates

/-!
# Chief counts from a binary section of the triple cover of A₆

A faithful irreducible binary action of the triple cover recovers its field
of four elements from the central cubic. Restricting a literal section to
an actor mapping onto that center therefore contributes one noncentral
binary chief factor per field dimension. The bound is expressed using the
original binary dimension, without a supplied scalar character or field action.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, 13.8.30,
printed p.964. The concrete cover retains the imported ATLAS attribution.
-/

public noncomputable section
open Subgroup Atlas.Codes NoncentralChiefRefinement
namespace Representation.Hexacode
open TwelveDimensional
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module Bit W]

/-- Recovering the central scalar action turns the original binary degree
into a lower bound for every complete chief series of the literal actor. -/
theorem binary_degree_le_twice_chief_count
    (D A N : Subgroup G)
    (σ : Representation Bit HexEvenAutomorphisms W) [IsIrreducible σ]
    (hf : Function.Injective σ) (π : D →* HexEvenAutomorphisms)
    (hπ : π.range = center HexEvenAutomorphisms)
    (d : BinaryConjugationSection D A N (σ.comp π))
    (t : ChiefSeries D) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    Module.finrank Bit W ≤ 2 * t.noncentralTwoCount := by
  let : Finite W := Finite.of_surjective
    (fun x : A => (d.coordinates x).toAdd) (Multiplicative.toAdd.surjective.comp d.onto)
  let hq := TwelveDimensional.scalar_quadratic σ hf
  let := TwelveDimensional.fieldModule σ hq
  let := TwelveDimensional.fieldTower σ hq
  let := field_finite σ hq
  let c : D →* center HexEvenAutomorphisms :=
    π.codRestrict _ (fun x => hπ ▸ (show π x ∈ π.range from ⟨x,rfl⟩))
  let χ : D →* Fˣ := centerCharacter.toMonoidHom.comp c
  have hχ : Function.Surjective χ := by
    intro a
    have ha : (centerCharacter.symm a).val ∈ π.range := by
      rw [hπ]
      exact (centerCharacter.symm a).property
    obtain ⟨x,hx⟩ := ha
    refine ⟨x,?_⟩
    change centerCharacter (c x) = a
    have he : c x = centerCharacter.symm a := Subtype.ext hx
    rw [he,centerCharacter.apply_symm_apply]
  have hn : ∃ x, χ x ≠ 1 := by
    let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [Nat.card_units,Nat.card_eq_fintype_card,field_card]
      decide)
    obtain ⟨a,ha⟩ := exists_ne (1 : Fˣ)
    obtain ⟨x,rfl⟩ := hχ a
    exact ⟨x,ha⟩
  have hscalar (x : D) (w : W) : (σ.comp π) x w = (χ x : F) • w :=
    centerCharacter_action (fieldRepresentation σ hq)
      (fieldRepresentation_scalar σ hq) (c x) w
  have hc := scalar_dimension_le_complete_count d χ hχ hn hscalar t ht0 ht1
  have hd := TwelveDimensional.field_finrank σ hq
  omega

end Representation.Hexacode
