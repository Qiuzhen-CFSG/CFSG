module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Action.Projection

/-!
# The remaining internal Sylow action in the linear branch

C.5.4(2),(4) separate the group-theoretic Baumann calculation from the choice
of natural-module coordinates. The former says that S ∩ L is Sylow in L and
that every S-action on the full U is induced by an element of S ∩ L. The
latter puts this Sylow action in upper-unipotent coordinates using the genuine
block module model. Both assertions below are unproved input predicates;
this file only assembles them and transports centralizer cosets to equal actions.

The source calculation remains an obligation even when the Sylow coordinate
calculation is proved. No target index or conjugate-module factorization is
included among these inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2),(4),
printed p.155, using B.6.9–10; C.5.6 (*), printed p.156.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices
open Subgroup
universe u
variable {G : Type u} [Group G]

/-- The group-theoretic part of C.5.4 for a linear block, before choosing a field basis. -/
structure InternalSylowAction (R L : Subgroup G) : Prop where
  normalizes : S R ≤ normalizer (U L : Set G)
  sylow : Chapter1.IsSylowIn 2 (S R ⊓ L) L
  internal : ∀ s : S R, ∃ t : S R, (t : G) ∈ L ∧
    ∀ v : U L, moduleConjugate normalizes s v = moduleConjugate normalizes t v

/-- The actual core-centralizer identity turns an internal coset representative
into an internal actor on the full commutator layer. -/
theorem internalSylowAction_of_core_cosets {H R L : Subgroup G}
    (hb : BaumannStructure H R L)
    (hn : S R ≤ normalizer (U L : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (S R ⊓ L) L)
    (hcosets : ∀ s : S R, ∃ t : S R, (t : G) ∈ L ∧ ((t : G)⁻¹ * s) ∈ Q R L) :
    InternalSylowAction R L := by
  refine ⟨hn, hSylow, ?_⟩
  intro s
  obtain ⟨t, ht, hq⟩ := hcosets s
  have hc := (hb.core_eq ▸ hq).2
  refine ⟨t, ht, ?_⟩
  intro v
  have he := hc (v : G) v.property
  apply Subtype.ext
  change (s : G) * (v : G) * (s : G)⁻¹ = (t : G) * (v : G) * (t : G)⁻¹
  have he' := congrArg (fun z : G => (t : G) * z * (s : G)⁻¹) he
  simpa [mul_assoc] using he'.symm

variable [Finite G]

/-- The remaining application of B.6.9–10 to the genuine local configuration. -/
def LinearInternalSylowInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ∀ n, ChapterC.IsL2EvenBlock L n → InternalSylowAction R L

/-- The independent natural-module calculation, with the source's internal
Sylow assertion explicit. Its proof must construct both coordinate maps. -/
def LinearSylowCoordinatesInput : Prop :=
  ∀ R L : Subgroup G, ∀ n, ChapterC.IsL2EvenBlock L n → InternalSylowAction R L →
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      ∃ c : ActionCoordinates R L F, c.IsInternal

omit [Finite G] in
/-- Assembly of the source group calculation and the natural Sylow coordinates.
Neither remaining premise is asserted by this conditional theorem. -/
theorem linearCoordinatesInput_of_internalSylow (K : GroupClass.{u})
    (hs : LinearInternalSylowInput (G := G) K)
    (hc : LinearSylowCoordinatesInput (G := G)) : LinearCoordinatesInput (G := G) K := by
  intro A H R L h hb n hL
  exact hc R L n hL (hs A H R L h hb n hL)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices

end
