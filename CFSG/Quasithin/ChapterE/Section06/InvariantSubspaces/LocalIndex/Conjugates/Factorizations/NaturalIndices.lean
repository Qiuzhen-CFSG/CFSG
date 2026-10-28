module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Transport
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Lifting
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Symmetry

/-!
# Assembly of the natural conjugate-action indices

The parameter map gives the Baumann actor index. The second-coordinate
kernel computes the full-module index against each nontrivial actor;
inverse-conjugation symmetry turns it into the required conjugate index.
The defining block-module cardinality supplies the remaining square index.
The witnesses are 2^n for L₂(2^n) and 2 for A₃.

The final theorem is conditional on constructing the actual action
coordinates and proving the intrinsic covering facts. Those inputs remain
outstanding; this module does not yet discharge NaturalIndicesInput.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.6 (*),
printed p.156 (PDF p.167), using C.5.4(2),(4) and I.2.3(1).
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices
open Subgroup
universe u
variable {G : Type u} [Group G] {K : GroupClass.{u}} {A H R L : Subgroup G}

/-- Applying the full fixed-space calculation to the inverse conjugate
computes the action index of the given conjugate. -/
theorem conjugate_index_of_fixedLift {F : Type*} [Field F]
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (c : ActionCoordinates R L F) (hlift : c.FixedLift) {x : G} (hx : x ∈ A)
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G)) :
    (centralizer (U L : Set G)).relIndex
      ((U L).map (MulAut.conj x).toMonoidHom) = Nat.card F := by
  rw [conjugate_index_eq_inverse]
  exact module_index_of_fixedLift c hlift _
    (conjugate_le_baumann h hb (A.inv_mem hx)) (inverse_not_centralizing _ _ hnc)

/-- Assembly of the two coordinate constructions and the two intrinsic
covering facts. All four inputs remain proof obligations of the source result. -/
theorem naturalIndicesInput_of_coordinates_and_covers (K : GroupClass.{u})
    (hl : LinearCoordinatesInput (G := G) K)
    (ha : AlternatingThreeCoordinatesInput (G := G) K)
    (hcover : LinearCoverInput (G := G)) (haz : AlternatingThreeCoverInput (G := G)) :
    NaturalIndicesInput (G := G) K := by
  intro A H R L h hb htype x hx hnc
  rcases htype with ⟨n, hn⟩ | ha3
  · obtain ⟨F, instF, instFinite, hF, c, hi⟩ := hl A H R L h hb n hn
    have hfix := fixedLift_of_linearCover c hcover hn hi
    refine ⟨2 ^ n, actionIndices_of_l2 hn ?_ ?_⟩
    · exact (actor_index c).trans hF
    · exact (conjugate_index_of_fixedLift h hb c hfix hx hnc).trans hF
  · obtain ⟨c⟩ := ha A H R L h hb ha3 (haz L ha3)
    have hfix := fixedLift_of_blockFixed_eq_bot c (haz L ha3)
    refine ⟨2, actionIndices_of_a3 ha3 ?_ ?_⟩
    · simpa only [Nat.card_zmod] using actor_index c
    · simpa only [Nat.card_zmod] using conjugate_index_of_fixedLift h hb c hfix hx hnc

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices
end
