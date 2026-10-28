/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleShapes.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleOddProfile
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleEvenProfile
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleShapes.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- Coordinate and Golay incidence classes, before any orbit assertion. -/
def Co3TriangleShape (a : Omega) : Fin 8 → leech → Prop
  | 0, y => y = oddMinimumVector a 0
  | 1, y => ∃ T : Finset Omega, T.card = 2 ∧ a ∉ T ∧ y.val = constantSupportVector 4 T
  | 2, y => ∃ c : golay, hammingNorm c.val = 16 ∧ c.val a = 1 ∧ y = oddMinimumVector a c
  | 3, y => ∃ b : Omega, ∃ c : golay, b ≠ a ∧ hammingNorm c.val = 8 ∧
      c.val a = 1 ∧ c.val b = 1 ∧ y = oddMinimumVector b c
  | 4, y => ∃ b : Omega, ∃ c : golay, b ≠ a ∧ hammingNorm c.val = 8 ∧
      c.val a = 0 ∧ c.val b = 0 ∧ y = oddMinimumVector b c
  | 5, y => ∃ T : Finset Omega, T ∈ octads ∧ ∃ s : T → Bit,
      (∃ ha : a ∈ T, s ⟨a,ha⟩ = 0) ∧ supportNegativeCount T s = 4 ∧
      y.val = (fun i => 2*signedSupport T s i)
  | 6, y => ∃ T : Finset Omega, T ∈ octads ∧ ∃ s : T → Bit,
      a ∉ T ∧ supportNegativeCount T s = 2 ∧ y.val = (fun i => 2*signedSupport T s i)
  | 7, y => ∃ b : Omega, ∃ c : golay, b ≠ a ∧ hammingNorm c.val = 12 ∧
      c.val a = 0 ∧ c.val b = 1 ∧ y = oddMinimumVector b c

theorem co3_triangle_shape_exhaustive (a : Omega) (y : Co3Triangles a) :
    ∃ t, Co3TriangleShape a t y.val := by
  have hd := ((co3_triangle_iff a y.val).mp y.prop).2
  rcases leech_coordinate_parity y.val.val y.val.prop with hp | hp
  · rcases co3_triangle_even_cases a y.val y.prop.1 hd hp with h | ⟨T,hT,s,hs,h⟩
    · exact ⟨1,h⟩
    · rcases h with ⟨ha,hn⟩ | ⟨ha,hz,hn⟩
      · exact ⟨6,T,hT,s,ha,hn,hs⟩
      · exact ⟨5,T,hT,s,⟨ha,hz⟩,hn,hs⟩
  · have hm := (odd_minimal_shell_iff y.val.val).mp ⟨y.val.prop,hp,y.prop.1⟩
    obtain ⟨b,c,hc⟩ := odd_minimum_parameterization y.val hm
    rw [← hc] at hd
    rcases co3_triangle_odd_cases a b c hd with
      ⟨rfl,rfl⟩ | ⟨rfl,hw,ha⟩ | ⟨hb,hw,ha,hb'⟩ | ⟨hb,hw,ha,hb'⟩ | ⟨hb,hw,ha,hb'⟩
    · exact ⟨0,hc.symm⟩
    · exact ⟨2,c,hw,ha,hc.symm⟩
    · exact ⟨4,b,c,hb,hw,ha,hb',hc.symm⟩
    · exact ⟨7,b,c,hb,hw,ha,hb',hc.symm⟩
    · exact ⟨3,b,c,hb,hw,ha,hb',hc.symm⟩

theorem scaled_signedSupport_norm (k : ℤ) (T : Finset Omega) (s : T → Bit) :
    integerDot (fun i => k*signedSupport T s i) (fun i => k*signedSupport T s i) =
      k*k*T.card := by
  have h := signedSupport_norm T s
  calc
    _ = k*k*integerDot (signedSupport T s) (signedSupport T s) := by
      simp only [integerDot,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    _ = _ := by rw [h]

theorem co3_triangle_shape_sound (a : Omega) (t : Fin 8) (y : leech)
    (h : Co3TriangleShape a t y) :
    integerDot y.val y.val = 32 ∧ integerDot (normSixVector a-y).val (normSixVector a-y).val = 64 := by
  apply (co3_triangle_iff a y).mpr
  fin_cases t
  · change y = oddMinimumVector a 0 at h
    subst y
    exact (co3_triangle_iff a _).mp (co3_base_triangle_norms a)
  · obtain ⟨T,hT,ha,hy⟩ := h
    constructor
    · rw [hy,constantSupport_norm,hT]; norm_num
    · rw [integerDot_normSix,hy]
      simp [constantSupportVector,ha,hT]
  · obtain ⟨c,hw,ha,rfl⟩ := h
    refine ⟨((odd_minimal_shell_iff _).mpr (oddMinimumVector_mem a c)).2.2,?_⟩
    rw [normSix_oddMinimum_dot]
    simp [hw,ha]
  · obtain ⟨b,c,hb,hw,ha,hb',rfl⟩ := h
    refine ⟨((odd_minimal_shell_iff _).mpr (oddMinimumVector_mem b c)).2.2,?_⟩
    rw [normSix_oddMinimum_dot]
    simp [hw,ha,hb',Ne.symm hb]
  · obtain ⟨b,c,hb,hw,ha,hb',rfl⟩ := h
    refine ⟨((odd_minimal_shell_iff _).mpr (oddMinimumVector_mem b c)).2.2,?_⟩
    rw [normSix_oddMinimum_dot]
    simp [hw,ha,hb',Ne.symm hb]
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,hy⟩ := h
    constructor
    · rw [hy,scaled_signedSupport_norm,octad_size T hT]; norm_num
    · rw [integerDot_normSix,hy,← Finset.mul_sum,signedSupport_sum]
      change 2*((T.card : ℤ)-2*supportNegativeCount T s)+4*(2*signedSupport T s a)=8
      rw [hn,octad_size T hT]
      simp [signedSupport,ha,hz]
  · obtain ⟨T,hT,s,ha,hn,hy⟩ := h
    constructor
    · rw [hy,scaled_signedSupport_norm,octad_size T hT]; norm_num
    · rw [integerDot_normSix,hy,← Finset.mul_sum,signedSupport_sum]
      change 2*((T.card : ℤ)-2*supportNegativeCount T s)+4*(2*signedSupport T s a)=8
      rw [hn,octad_size T hT]
      simp [signedSupport,ha]
  · obtain ⟨b,c,hb,hw,ha,hb',rfl⟩ := h
    refine ⟨((odd_minimal_shell_iff _).mpr (oddMinimumVector_mem b c)).2.2,?_⟩
    rw [normSix_oddMinimum_dot]
    simp [hw,ha,hb',Ne.symm hb]

theorem co3_triangle_shapes_iff (a : Omega) (y : leech) :
    (∃ t, Co3TriangleShape a t y) ↔
      integerDot y.val y.val = 32 ∧ integerDot (normSixVector a-y).val (normSixVector a-y).val = 64 :=
  ⟨fun ⟨t,ht⟩ => co3_triangle_shape_sound a t y ht,
    fun h => co3_triangle_shape_exhaustive a ⟨y,h⟩⟩

end Atlas.Conway
