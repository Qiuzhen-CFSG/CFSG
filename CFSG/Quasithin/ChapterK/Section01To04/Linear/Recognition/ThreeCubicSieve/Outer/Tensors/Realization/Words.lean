module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Character
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Words.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Words.Forms
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Words.Pairing

/-!
# Assembly of paired component coordinates from SL₃ word geometry

The actual Schur-linear lift preserves the repeated-word character. The graph
calculation rules out the pure graph alternative, and a half-turn form forces
an explicit pairing of its factors. The tensor equivalence then supplies
coordinates for the original lifted automorphism on the central cover.

The proved automorphism normal forms and tensor construction discharge both
geometric inputs of the assembly. The supplied actor lift remains explicit,
as required by `NaturalPairedCoordinates`; the half representation lives on
SL₃ and need not descend through the central kernel of the full action.
Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.8,
steps 2--5, manuscript pp.26--28; Aschbacher--Smith K.3.2, printed pp.454--456.
-/

public section
noncomputable section
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The normal-form and tensor-geometry inputs give the published coordinates,
with graph exclusion and the literal half-word relation discharged here. -/
theorem natural_paired_coordinates_of_forms_and_pairing
    (hforms : OuterInvolutionForms B σ) (hpair : HalfTurnWordPairing B σ) :
    NaturalPairedCoordinates B σ := by
  intro M hn _ t hout ht L
  rcases hforms t hout ht L with hgraph | hfield
  · obtain ⟨m, hm⟩ := hgraph
    exact (L.not_linear_graph ht M hn m hm).elim
  · obtain ⟨H⟩ := hfield
    have hχ := L.word_character_fixed ht M
    exact hpair M L.automorphism H (H.half_naturalCount_pos M hn hχ) (H.word_pair M hχ)

/-- Every natural-containing repeated model has paired component coordinates
for the supplied Schur-linear outer involution lift. The normal-form and tensor
equivalence premises are discharged, retaining the actual central cover and
GL₃ twist. This supplies the coordinate input to the natural swap assembly. -/
theorem natural_paired_coordinates (hk : σ.ker ≤ Subgroup.center SL(3,B.Carrier)) :
    NaturalPairedCoordinates B σ :=
  natural_paired_coordinates_of_forms_and_pairing B σ
    (outer_involution_forms B σ hk) (half_turn_word_pairing B σ)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
