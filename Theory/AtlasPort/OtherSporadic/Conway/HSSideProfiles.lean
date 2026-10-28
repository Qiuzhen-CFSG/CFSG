/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSSideProfiles.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSModel
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleShapeIndex

/-!
Coordinate restrictions on possible norm-four sides of the marked triangle.
The minimum-vector shape classification reduces the pairings to support and sign constraints.

Source: Gerald Höhn, `Atlas/Conway/HSSideProfiles.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem hs_side_odd_cases (a b : Omega) (c : golay)
    (hd : integerDot (normSixVector a).val (oddMinimumVector b c).val = 16) :
    (b = a ∧ hammingNorm c.val = 12 ∧ c.val a = 1) ∨
    (b ≠ a ∧ hammingNorm c.val = 8 ∧ c.val a = 0 ∧ c.val b = 1) := by
  rw [normSix_oddMinimum_dot] at hd
  have hw := golay_weights c
  change hammingNorm c.val = 0 ∨ hammingNorm c.val = 8 ∨ hammingNorm c.val = 12 ∨
    hammingNorm c.val = 16 ∨ hammingNorm c.val = 24 at hw
  by_cases hab : b = a
  · subst b
    rcases bit_cases (c.val a) with hc | hc
    · simp [hc] at hd; omega
    · left; refine ⟨rfl,?_,hc⟩
      simp [hc] at hd; omega
  · rcases bit_cases (c.val a) with ha | ha <;> rcases bit_cases (c.val b) with hb | hb
    · simp [ha,hb,Ne.symm hab] at hd; omega
    · right; refine ⟨hab,?_,ha,hb⟩
      simp [ha,hb,Ne.symm hab] at hd; omega
    · have hz : hammingNorm c.val = 0 := by simp [ha,hb,Ne.symm hab] at hd; omega
      have he := congrFun (hammingNorm_eq_zero.mp hz) a
      rw [ha] at he
      norm_num at he
    · simp [ha,hb,Ne.symm hab] at hd; omega

theorem hs_side_four_signs (a : Omega) (T : Finset Omega) (hT : T.card = 2)
    (s : T → Bit)
    (hd : (∑ i, 4*signedSupport T s i)+4*(4*signedSupport T s a) = 16) :
    ∃ ha : a ∈ T, s ⟨a,ha⟩ = 0 ∧ supportNegativeCount T s = 1 := by
  rw [← Finset.mul_sum,signedSupport_sum] at hd
  change 4*((T.card : ℤ)-2*supportNegativeCount T s)+4*(4*signedSupport T s a)=16 at hd
  rw [hT] at hd
  have hb := supportNegativeCount_bounds T s
  have ha : a ∈ T := by
    by_contra ha
    simp [signedSupport,ha] at hd; omega
  refine ⟨ha,?_,?_⟩
  · rcases bit_cases (s ⟨a,ha⟩) with hs | hs
    · exact hs
    · simp [signedSupport,ha,hs] at hd; omega
  · rcases bit_cases (s ⟨a,ha⟩) with hs | hs <;>
      simp [signedSupport,ha,hs] at hd <;> omega

theorem hs_side_octad_signs (a : Omega) (T : Finset Omega) (hT : T.card = 8)
    (s : T → Bit)
    (hd : (∑ i, 2*signedSupport T s i)+4*(2*signedSupport T s a) = 16) :
    (a ∉ T ∧ supportNegativeCount T s = 0) ∨
    (∃ ha : a ∈ T, s ⟨a,ha⟩ = 0 ∧ supportNegativeCount T s = 2) := by
  rw [← Finset.mul_sum,signedSupport_sum] at hd
  change 2*((T.card : ℤ)-2*supportNegativeCount T s)+4*(2*signedSupport T s a)=16 at hd
  rw [hT] at hd
  have hb := supportNegativeCount_bounds T s
  by_cases ha : a ∈ T
  · right
    rcases bit_cases (s ⟨a,ha⟩) with hs | hs
    · refine ⟨ha,hs,?_⟩
      simp [signedSupport,ha,hs] at hd; omega
    · simp [signedSupport,ha,hs] at hd; omega
  · left; refine ⟨ha,?_⟩
    simp [signedSupport,ha] at hd; omega

/-- Independent coordinate classes of norm-four sides, before transitivity. -/
def HSSideShape (a : Omega) : Fin 5 → leech → Prop
  | 0, y => ∃ T : Finset Omega, T.card = 2 ∧ ∃ s : T → Bit,
      (∃ ha : a ∈ T, s ⟨a,ha⟩ = 0) ∧ supportNegativeCount T s = 1 ∧
      y.val = (fun i => 4*signedSupport T s i)
  | 1, y => ∃ T : Finset Omega, T ∈ octads ∧ a ∉ T ∧
      y.val = constantSupportVector 2 T
  | 2, y => ∃ T : Finset Omega, T ∈ octads ∧ ∃ s : T → Bit,
      (∃ ha : a ∈ T, s ⟨a,ha⟩ = 0) ∧ supportNegativeCount T s = 2 ∧
      y.val = (fun i => 2*signedSupport T s i)
  | 3, y => ∃ b : Omega, ∃ c : golay, b ≠ a ∧ hammingNorm c.val = 8 ∧
      c.val a = 0 ∧ c.val b = 1 ∧ y = oddMinimumVector b c
  | 4, y => ∃ c : golay, hammingNorm c.val = 12 ∧ c.val a = 1 ∧
      y = oddMinimumVector a c

theorem hs_side_shape_exhaustive (a : Omega) (y : leech)
    (hy : integerDot y.val y.val = 32)
    (hd : integerDot (normSixVector a).val y.val = 16) :
    ∃ t, HSSideShape a t y := by
  rcases leech_coordinate_parity y.val y.prop with hp | hp
  · rw [integerDot_normSix] at hd
    rcases Finset.mem_union.mp ((even_minimal_shell_iff y.val).mp ⟨y.prop,hp,hy⟩) with h | h
    · obtain ⟨T,hT,s,hs⟩ := minimum_four_parameterization y h
      rw [hs] at hd
      obtain ⟨ha,hz,hn⟩ := hs_side_four_signs a T hT s hd
      exact ⟨0,T,hT,s,⟨ha,hz⟩,hn,hs⟩
    · obtain ⟨T,hT,hC,s,_,hs⟩ := minimum_octad_parameterization y h
      rw [hs] at hd
      rcases hs_side_octad_signs a T hT s hd with ⟨ha,hn⟩ | ⟨ha,hz,hn⟩
      · refine ⟨1,T,codeSupport_octad T hT hC,ha,hs.trans ?_⟩
        have hz := supportNegativeCount_zero T s hn
        funext i
        by_cases hi : i ∈ T <;> simp [signedSupport,constantSupportVector,hi,hz]
      · exact ⟨2,T,codeSupport_octad T hT hC,s,⟨ha,hz⟩,hn,hs⟩
  · have hm := (odd_minimal_shell_iff y.val).mp ⟨y.prop,hp,hy⟩
    obtain ⟨b,c,hc⟩ := odd_minimum_parameterization y hm
    rw [← hc] at hd
    rcases hs_side_odd_cases a b c hd with ⟨rfl,hw,ha⟩ | ⟨hb,hw,ha,hb'⟩
    · exact ⟨4,c,hw,ha,hc.symm⟩
    · exact ⟨3,b,c,hb,hw,ha,hb',hc.symm⟩

end Atlas.Conway
