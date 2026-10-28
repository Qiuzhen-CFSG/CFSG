/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleShapeIndex.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleParameterMap
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleShapeIndex.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- A coordinate invariant distinguishing the eight incidence classes. -/
def co3TriangleCoordinateType (a : Omega) (y : IntegerCoordinates) : Fin 8 :=
  if y a % 2 = 0 then
    if y a = 2 then 5 else if ∃ i, y i = 4 then 1 else 6
  else if y a = -3 then 0 else if y a = 3 then 2 else if y a = -1 then 3
    else if ∃ i, y i = 3 then 7 else 4

theorem oddMinimumVector_apply (b : Omega) (c : golay) (i : Omega) :
    (oddMinimumVector b c).val i =
      if c.val i = 0 then (if i = b then -3 else 1) else (if i = b then 3 else -1) := by
  simp [oddMinimumVector,signedOddProfile,signChange,oddProfileBase]
  split_ifs <;> norm_num

theorem oddMinimumVector_three_iff (b : Omega) (c : golay) :
    (∃ i, (oddMinimumVector b c).val i = 3) ↔ c.val b = 1 := by
  constructor
  · rintro ⟨i,hi⟩
    rw [oddMinimumVector_apply] at hi
    by_cases hb : i = b
    · subst i
      rcases bit_cases (c.val b) with hc | hc <;> simp_all
    · split_ifs at hi; omega
  · intro hc
    exact ⟨b,by simp [oddMinimumVector_apply,hc]⟩

theorem co3_triangle_odd_coordinate_type (a b : Omega) (c : golay) :
    co3TriangleCoordinateType a (oddMinimumVector b c).val =
      if b = a then (if c.val a = 0 then 0 else 2)
      else if c.val a = 1 then 3 else if c.val b = 1 then 7 else 4 := by
  unfold co3TriangleCoordinateType
  simp only [oddMinimumVector_three_iff]
  simp only [oddMinimumVector_apply]
  by_cases hb : b = a
  · subst b
    rcases bit_cases (c.val a) with ha | ha <;> simp [ha]
  · rcases bit_cases (c.val a) with ha | ha <;> rcases bit_cases (c.val b) with hc | hc <;>
      simp [hb,Ne.symm hb,ha,hc]

theorem co3_triangle_shape_coordinate_type (a : Omega) (t : Fin 8) (y : leech)
    (h : Co3TriangleShape a t y) : co3TriangleCoordinateType a y.val = t := by
  fin_cases t
  · change y = oddMinimumVector a 0 at h
    rw [h,co3_triangle_odd_coordinate_type]; simp
  · obtain ⟨T,hT,ha,hy⟩ := h
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i,hi⟩ := hne
    have hex : ∃ i, constantSupportVector 4 T i = 4 := ⟨i,by simp [constantSupportVector,hi]⟩
    rw [hy]
    have hz : constantSupportVector 4 T a = 0 := by simp [constantSupportVector,ha]
    simp only [co3TriangleCoordinateType,hz,hex]
    norm_num
  · obtain ⟨c,hw,ha,rfl⟩ := h
    rw [co3_triangle_odd_coordinate_type]; simp [ha]
  · obtain ⟨b,c,hb,hw,ha,hc,rfl⟩ := h
    rw [co3_triangle_odd_coordinate_type]; simp [hb,ha]
  · obtain ⟨b,c,hb,hw,ha,hc,rfl⟩ := h
    rw [co3_triangle_odd_coordinate_type]; simp [hb,ha,hc]
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,hy⟩ := h
    rw [hy]
    simp [co3TriangleCoordinateType,signedSupport,ha,hz]
  · obtain ⟨T,hT,s,ha,hn,hy⟩ := h
    have hn4 : ¬∃ i, 2*signedSupport T s i = 4 := by
      rintro ⟨i,hi⟩
      simp only [signedSupport] at hi
      split_ifs at hi <;> omega
    rw [hy]
    have hz : 2*signedSupport T s a = 0 := by simp [signedSupport,ha]
    simp only [co3TriangleCoordinateType,hz,hn4]
    norm_num; rfl
  · obtain ⟨b,c,hb,hw,ha,hc,rfl⟩ := h
    rw [co3_triangle_odd_coordinate_type]; simp [hb,ha,hc]

theorem co3_triangle_shape_unique (a : Omega) (s t : Fin 8) (y : leech)
    (hs : Co3TriangleShape a s y) (ht : Co3TriangleShape a t y) : s = t :=
  (co3_triangle_shape_coordinate_type a s y hs).symm.trans
    (co3_triangle_shape_coordinate_type a t y ht)

end Atlas.Conway
