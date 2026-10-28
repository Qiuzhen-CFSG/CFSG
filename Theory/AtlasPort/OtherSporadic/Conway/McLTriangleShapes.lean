/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLTriangleShapes.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLTriangleStabilizer
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleShapeIndex

/-!
Four coordinate shapes for the McLaughlin triangle slice.
The established Conway3 coordinate classification and the two marked pairings
give exhaustive, unique and sound shape predicates.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLTriangleShapes.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- The four marked Golay incidence classes in the McLaughlin triangle slice. -/
def McLTriangleShape : Fin 4 → leech → Prop
  | 0, y => y = mclReferenceVector
  | 1, y => ∃ c : golay, hammingNorm c.val = 8 ∧
      c.val co3MarkedCoordinate = 0 ∧ c.val co3BasePoint.val = 0 ∧
      y = oddMinimumVector co3BasePoint.val c
  | 2, y => ∃ b : Omega, ∃ c : golay,
      b ≠ co3MarkedCoordinate ∧ b ≠ co3BasePoint.val ∧ hammingNorm c.val = 8 ∧
      c.val co3MarkedCoordinate = 1 ∧ c.val co3BasePoint.val = 1 ∧ c.val b = 1 ∧
      y = oddMinimumVector b c
  | 3, y => ∃ T : Finset Omega, T ∈ octads ∧ ∃ s : T → Bit,
      co3MarkedCoordinate ∉ T ∧ supportNegativeCount T s = 2 ∧
      (∃ hp : co3BasePoint.val ∈ T, s ⟨co3BasePoint.val,hp⟩ = 1) ∧
      y.val = (fun i => 2*signedSupport T s i)

theorem mcl_triangle_coordinate_sum (y : McLTriangles) :
    y.val.val co3MarkedCoordinate + y.val.val co3BasePoint.val = -2 := by
  have h := y.prop.2.2
  change integerDot (minimumPairPlus _ _).val y.val.val = -8 at h
  rw [minimumPairPlus_dot] at h
  omega

theorem mcl_triangle_shape_exhaustive (y : McLTriangles) :
    ∃ t, McLTriangleShape t y.val := by
  have hsum := mcl_triangle_coordinate_sum y
  have htri : y.val ∈ {v : leech | integerDot v.val v.val = 32 ∧
      integerDot ((normSixVector co3MarkedCoordinate)-v).val
        ((normSixVector co3MarkedCoordinate)-v).val = 64} :=
    (co3_triangle_iff _ _).mpr ⟨y.prop.1,y.prop.2.1⟩
  obtain ⟨t,ht⟩ := co3_triangle_shape_exhaustive co3MarkedCoordinate ⟨y.val,htri⟩
  have hpa : co3BasePoint.val ≠ co3MarkedCoordinate := co3BasePoint.prop
  fin_cases t
  · exact ⟨0,ht⟩
  · obtain ⟨T,hT,ha,hy⟩ := ht
    rw [hy] at hsum
    simp only [constantSupportVector,if_neg ha] at hsum
    split_ifs at hsum <;> omega
  · obtain ⟨c,hw,ha,hy⟩ := ht
    rw [hy] at hsum
    rcases bit_cases (c.val co3BasePoint.val) with hp | hp <;>
      simp [oddMinimumVector_apply,ha,hp,hpa] at hsum
  · obtain ⟨b,c,hb,hw,ha,hc,hy⟩ := ht
    rw [hy] at hsum
    have hpb : b ≠ co3BasePoint.val := by
      intro hh; subst b
      simp [oddMinimumVector_apply,ha,hc,Ne.symm hpa] at hsum
    have hp : c.val co3BasePoint.val = 1 := by
      rcases bit_cases (c.val co3BasePoint.val) with hp | hp
      · simp [oddMinimumVector_apply,ha,hp,Ne.symm hb,Ne.symm hpb] at hsum
      · exact hp
    exact ⟨2,b,c,hb,hpb,hw,ha,hp,hc,hy⟩
  · obtain ⟨b,c,hb,hw,ha,hc,hy⟩ := ht
    rw [hy] at hsum
    have hpb : b = co3BasePoint.val := by
      by_contra hh
      rcases bit_cases (c.val co3BasePoint.val) with hp | hp <;>
        simp [oddMinimumVector_apply,ha,hp,Ne.symm hb,Ne.symm hh] at hsum
    subst b
    exact ⟨1,c,hw,ha,hc,hy⟩
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,hy⟩ := ht
    rw [hy] at hsum
    simp only [signedSupport,dif_pos ha,if_pos hz] at hsum
    split_ifs at hsum <;> omega
  · obtain ⟨T,hT,s,ha,hn,hy⟩ := ht
    rw [hy] at hsum
    have hp : co3BasePoint.val ∈ T := by
      by_contra hp
      simp [signedSupport,ha,hp] at hsum
    have hs : s ⟨co3BasePoint.val,hp⟩ = 1 := by
      rcases bit_cases (s ⟨co3BasePoint.val,hp⟩) with hz | hz
      · simp [signedSupport,ha,hp,hz] at hsum
      · exact hz
    exact ⟨3,T,hT,s,ha,hn,⟨hp,hs⟩,hy⟩
  · obtain ⟨b,c,hb,hw,ha,hc,hy⟩ := ht
    rw [hy] at hsum
    by_cases hpb : co3BasePoint.val = b
    · simp [oddMinimumVector_apply,ha,hc,hpb,Ne.symm hb] at hsum
    · rcases bit_cases (c.val co3BasePoint.val) with hp | hp <;>
        simp [oddMinimumVector_apply,ha,hp,Ne.symm hb,hpb] at hsum

theorem mcl_triangle_shape_coordinate_pair (t : Fin 4) (y : leech)
    (h : McLTriangleShape t y) :
    (y.val co3MarkedCoordinate,y.val co3BasePoint.val) =
      ![(-3,1),(1,-3),(-1,-1),(0,-2)] t := by
  have hpa : co3BasePoint.val ≠ co3MarkedCoordinate := co3BasePoint.prop
  fin_cases t
  · change y = mclReferenceVector at h
    rw [h]
    simp [mclReferenceVector,oddMinimumVector_zero_apply,hpa]
  · obtain ⟨c,hw,ha,hp,rfl⟩ := h
    simp [oddMinimumVector_apply,ha,hp,Ne.symm hpa]
  · obtain ⟨b,c,hb,hbp,hw,ha,hp,hc,rfl⟩ := h
    simp [oddMinimumVector_apply,ha,hp,Ne.symm hb,Ne.symm hbp]
  · obtain ⟨T,hT,s,ha,hn,⟨hp,hs⟩,hy⟩ := h
    rw [hy]
    simp [signedSupport,ha,hp,hs]

theorem mcl_triangle_shape_unique (s t : Fin 4) (y : leech)
    (hs : McLTriangleShape s y) (ht : McLTriangleShape t y) : s = t := by
  have h := (mcl_triangle_shape_coordinate_pair s y hs).symm.trans
    (mcl_triangle_shape_coordinate_pair t y ht)
  fin_cases s <;> fin_cases t <;> norm_num at *

theorem mcl_triangle_shape_sound (t : Fin 4) (y : leech)
    (h : McLTriangleShape t y) :
    integerDot y.val y.val = 32 ∧ integerDot (normSixVector co3MarkedCoordinate).val y.val = 8 ∧
      integerDot mclEndpoint.val y.val = -8 := by
  have hpair := mcl_triangle_shape_coordinate_pair t y h
  have hco : ∃ k, Co3TriangleShape co3MarkedCoordinate k y := by
    fin_cases t
    · exact ⟨0,h⟩
    · obtain ⟨c,hw,ha,hp,hy⟩ := h
      exact ⟨4,co3BasePoint.val,c,co3BasePoint.prop,hw,ha,hp,hy⟩
    · obtain ⟨b,c,hb,hbp,hw,ha,hp,hc,hy⟩ := h
      exact ⟨3,b,c,hb,hw,ha,hc,hy⟩
    · obtain ⟨T,hT,s,ha,hn,hp,hy⟩ := h
      exact ⟨6,T,hT,s,ha,hn,hy⟩
  have hc := (co3_triangle_iff _ _).mp ((co3_triangle_shapes_iff _ _).mp hco)
  refine ⟨hc.1,hc.2,?_⟩
  change integerDot (minimumPairPlus _ _).val y.val = -8
  rw [minimumPairPlus_dot]
  have h1 := congrArg Prod.fst hpair
  have h2 := congrArg Prod.snd hpair
  fin_cases t <;> norm_num at h1 h2 <;> rw [h1,h2] <;> norm_num

end Atlas.Conway
