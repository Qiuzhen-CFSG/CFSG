/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSGraphCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSGraphVertices

/-!
The concrete 100-point Higman–Sims configuration.
The Witt vertex map is bijective, with one base vertex, 22 points, and 77 hexads.

Source: Gerald Höhn, `Atlas/Conway/HSGraphCount.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem hs_point_dot (b : Mathieu23Points co3MarkedCoordinate) :
    integerDot hsEndpoint.val (minimumPairPlus co3MarkedCoordinate b.val).val =
      if b = co3BasePoint then 0 else 16 := by
  change integerDot (minimumPairMinus _ _).val _ = _
  rw [minimumPairMinus_dot]
  have hba : b.val ≠ co3MarkedCoordinate := b.prop
  have hpa : co3BasePoint.val ≠ co3MarkedCoordinate := co3BasePoint.prop
  by_cases hb : b = co3BasePoint
  · subst b
    simp [minimumPairPlus,coordinateVector,hpa,Ne.symm hpa]
  · have hbp : b.val ≠ co3BasePoint.val := fun h => hb (Subtype.ext h)
    simp [minimumPairPlus,coordinateVector,hpa,
      Ne.symm hba,Ne.symm hbp,hb]

theorem hs_heptad_dot (B : Co3Heptads co3MarkedCoordinate) :
    integerDot hsEndpoint.val (co3HeptadEndpoint co3MarkedCoordinate B).val =
      if co3BasePoint ∈ B.val then 0 else 8 := by
  change integerDot (minimumPairMinus _ _).val _ = _
  rw [minimumPairMinus_dot,co3HeptadEndpoint_marked,co3HeptadEndpoint_other]
  split_ifs <;> norm_num

theorem hs_complement_dot (u : leech) :
    integerDot hsEndpoint.val (normSixVector co3MarkedCoordinate-u).val =
      16-integerDot hsEndpoint.val u.val := by
  change integerDot _ ((normSixVector co3MarkedCoordinate).val-u.val)=_
  rw [integerDot_sub_right,integerDot_comm hsEndpoint.val,hs_normSix_endpoint_dot]

def hsGraphDecomposition (y : HSGraphPoints) : Atlas.Sporadic.Conway3.Points :=
  ⟨{y.val,normSixVector co3MarkedCoordinate-y.val},y.val,y.prop.1,by
    change integerDot (normSixVector co3MarkedCoordinate-y.val).val
      (normSixVector co3MarkedCoordinate-y.val).val = 32
    rw [leech_norm_sub,normSixVector_norm,y.prop.1,y.prop.2.1]
    norm_num,rfl⟩

theorem hsGraphDecomposition_injective : Function.Injective hsGraphDecomposition := by
  intro y z he
  have hp : ({y.val,normSixVector co3MarkedCoordinate-y.val} : Finset leech) =
      {z.val,normSixVector co3MarkedCoordinate-z.val} := congrArg Subtype.val he
  have hm : y.val ∈ ({z.val,normSixVector co3MarkedCoordinate-z.val} : Finset leech) := by
    rw [← hp]; exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hm with h | h
  · exact Subtype.ext h
  · have hd := y.prop.2.2
    rw [Finset.mem_singleton.mp h,hs_complement_dot,z.prop.2.2] at hd
    omega

theorem hsWittGraphMap_surjective : Function.Surjective hsWittGraphMap := by
  intro y
  obtain ⟨p,hp⟩ := (co3PointHeptadDecompositionEquiv co3MarkedCoordinate).surjective (hsGraphDecomposition y)
  have hm : y.val ∈ (co3PointHeptadDecompositionEquiv co3MarkedCoordinate p).val := by
    rw [hp]
    exact Finset.mem_insert_self _ _
  change y.val ∈ ({(co3EvenEndpointMap _ p).val,
    normSixVector co3MarkedCoordinate-(co3EvenEndpointMap _ p).val} : Finset leech) at hm
  rcases Finset.mem_insert.mp hm with he | he
  · cases p with
    | inl b =>
      change y.val = minimumPairPlus co3MarkedCoordinate b.val at he
      have hd := y.prop.2.2
      rw [he,hs_point_dot] at hd
      have hb : b ≠ co3BasePoint := by intro h; rw [if_pos h] at hd; omega
      exact ⟨Sum.inr (Sum.inl ⟨b,hb⟩),Subtype.ext he.symm⟩
    | inr B =>
      change y.val = co3HeptadEndpoint co3MarkedCoordinate B at he
      have hd := y.prop.2.2
      rw [he,hs_heptad_dot] at hd
      split_ifs at hd <;> omega
  · have he := Finset.mem_singleton.mp he
    cases p with
    | inl b =>
      change y.val = normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate b.val at he
      have hd := y.prop.2.2
      rw [he,hs_complement_dot,hs_point_dot] at hd
      have hb : b = co3BasePoint := by by_contra h; rw [if_neg h] at hd; omega
      subst b
      exact ⟨Sum.inl (),Subtype.ext he.symm⟩
    | inr B =>
      change y.val = normSixVector co3MarkedCoordinate-co3HeptadEndpoint co3MarkedCoordinate B at he
      have hd := y.prop.2.2
      rw [he,hs_complement_dot,hs_heptad_dot] at hd
      have hb : co3BasePoint ∈ B.val := by by_contra h; rw [if_neg h] at hd; omega
      exact ⟨Sum.inr (Sum.inr ⟨B,hb⟩),Subtype.ext he.symm⟩

def hsWittVertexEquiv : HSWittVertices ≃ HSGraphPoints :=
  Equiv.ofBijective hsWittGraphMap ⟨hsWittGraphMap_injective,hsWittGraphMap_surjective⟩

theorem hs_point_labels_card : Nat.card HSPointLabels = 22 := mathieu22_degree _ _

theorem hs_hexad_labels_card : Nat.card HSHexadLabels = 77 := co3_heptads_through_card _ _

instance : Finite HSGraphPoints := Finite.of_equiv _ hsWittVertexEquiv

theorem hs_graph_card : Nat.card HSGraphPoints = 100 := by
  rw [← Nat.card_congr hsWittVertexEquiv]
  change Nat.card (Unit ⊕ (HSPointLabels ⊕ HSHexadLabels)) = 100
  rw [Nat.card_sum,Nat.card_sum,hs_point_labels_card,hs_hexad_labels_card]
  norm_num

end Atlas.Conway
