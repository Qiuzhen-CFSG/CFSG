module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.Catalogue
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.ActorBounds
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.NaturalDescent
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.SupportShape
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.TensorDescent

/-!
# Representation recognition for K.3.4

The ambient cubic action selects one factor repeated once or twice in the
full periodic symplectic tensor catalogue. Descending the singleton gives
the published natural identification. Descending the repeated pair gives
the actual quadratic extension of the component's Schur field and an
intertwiner with the natural module tensored with its relative Frobenius
twist. The half parameter is the degree of that original Schur field.

`source_natural_or_tensor` discharges both selection and descent from the
genuine source hypotheses, for any class K and hence for the full known-simple
class. The binary degrees follow from the constructed intertwiners. This is
the representation-recognition step; the natural and tensor geometry supply
the remaining offender and ratio assertions of K.3.4.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, printed
pp.451,456--457, especially the application of GM04 Proposition 6.2 and Table 9;
GLS3, 2.8.6(a), Remark 2.8.8 and Examples 2.8.10(d).
-/

public section

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition
open Representation
open Theory.SpecificGroups.SymplecticFour

variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The representation-recognition step of K.3.4. The tensor alternative uses
the original component's Schur field, its quadratic embedding into F, and a
genuine scalar-extension intertwiner. No selection or degree premise remains. -/
theorem source_natural_or_tensor {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F) :
    letI := h.irreducible
    Nonempty (NaturalIdentification (F := F) (ρ.comp L.subtype)) ∨
      ∃ s : ℕ, 0 < s ∧ r = 2*s ∧
        ∃ a : Algebra (SchurField (ρ.comp L.subtype)) F, letI := a
          Nonempty (TensorIdentification (ρ.comp L.subtype) F s) := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨P, ha, ht | ht⟩ := source_selected_tensorParameters h hr hF e
  · exact Or.inl (P.natural (ρ.comp L.subtype) hr hF ha ht)
  · obtain ⟨hs, hrs, _⟩ := P.half_degree ha ht
    exact Or.inr ⟨Module.finrank (ZMod 2) (SchurField (ρ.comp L.subtype)), hs, hrs,
      P.tensor (ρ.comp L.subtype) hr hF ha ht⟩

/-- The two binary degrees in K.3.4, obtained from the actual representation
identifications rather than used as assumptions for recognition. -/
theorem source_binary_degrees {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F) :
    Module.finrank (ZMod 2) V = 4*r ∨
      ∃ s : ℕ, 0 < s ∧ r = 2*s ∧ Module.finrank (ZMod 2) V = 16*s := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  rcases source_natural_or_tensor h hr hF e with hnat | htensor
  · obtain ⟨η⟩ := hnat
    exact Or.inl (η.finrank hF)
  · obtain ⟨s, hs, hrs, a, ⟨η⟩⟩ := htensor
    let := a
    exact Or.inr ⟨s, hs, hrs, η.binary_finrank⟩

end CFSG.Quasithin.ChapterK.Symplectic.Recognition
