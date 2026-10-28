/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleEvenProfile.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleGeometry
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleEvenProfile.lean`, ATLAS revision
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

def supportNegativeCount (T : Finset Omega) (s : T → Bit) : ℤ :=
  ∑ i : T, if s i = 0 then 0 else 1

theorem supportNegativeCount_bounds (T : Finset Omega) (s : T → Bit) :
    0 ≤ supportNegativeCount T s ∧ supportNegativeCount T s ≤ T.card := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> omega)
  · calc
      _ ≤ ∑ _i : T, (1 : ℤ) := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
      _ = _ := by simp

theorem supportNegativeCount_pos (T : Finset Omega) (s : T → Bit)
    (i : T) (hi : s i ≠ 0) : 1 ≤ supportNegativeCount T s := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : T => if s j = 0 then (0 : ℤ) else 1)
    (fun j _ => by split_ifs <;> omega) (Finset.mem_univ i)
  simpa [supportNegativeCount,hi] using h

theorem supportNegativeCount_zero (T : Finset Omega) (s : T → Bit)
    (h : supportNegativeCount T s = 0) : ∀ i, s i = 0 := by
  intro i
  by_contra hi
  have := supportNegativeCount_pos T s i hi
  omega

theorem supportNegativeCount_lt (T : Finset Omega) (s : T → Bit)
    (i : T) (hi : s i = 0) : supportNegativeCount T s < T.card := by
  have h : (∑ j : T, if s j = 0 then (0 : ℤ) else 1) < ∑ _j : T, (1 : ℤ) := by
    apply Finset.sum_lt_sum
    · intro j _; split_ifs <;> omega
    · exact ⟨i,Finset.mem_univ i,by simp [hi]⟩
  simpa [supportNegativeCount] using h

theorem co3_triangle_four_signs (a : Omega) (T : Finset Omega) (hT : T.card = 2)
    (s : T → Bit)
    (hd : (∑ i, 4*signedSupport T s i)+4*(4*signedSupport T s a) = 8) :
    a ∉ T ∧ ∀ i, s i = 0 := by
  rw [← Finset.mul_sum,signedSupport_sum] at hd
  change 4*((T.card : ℤ)-2*supportNegativeCount T s)+4*(4*signedSupport T s a)=8 at hd
  rw [hT] at hd
  have hb := supportNegativeCount_bounds T s
  rw [hT] at hb
  have ha : a ∉ T := by
    intro ha
    rcases bit_cases (s ⟨a,ha⟩) with hs | hs
    · have hp := supportNegativeCount_lt T s ⟨a,ha⟩ hs
      rw [hT] at hp
      simp [signedSupport,ha,hs] at hd; omega
    · simp [signedSupport,ha,hs] at hd; omega
  refine ⟨ha,supportNegativeCount_zero T s ?_⟩
  simp [signedSupport,ha] at hd
  omega

/-- The two signed-octad possibilities are forced by the triangle inner product. -/
theorem co3_triangle_octad_signs (a : Omega) (T : Finset Omega) (hT : T.card = 8)
    (s : T → Bit)
    (hd : (∑ i, 2*signedSupport T s i)+4*(2*signedSupport T s a) = 8) :
    (a ∉ T ∧ supportNegativeCount T s = 2) ∨
    (∃ ha : a ∈ T, s ⟨a,ha⟩ = 0 ∧ supportNegativeCount T s = 4) := by
  rw [← Finset.mul_sum,signedSupport_sum] at hd
  change 2*((T.card : ℤ)-2*supportNegativeCount T s)+4*(2*signedSupport T s a)=8 at hd
  rw [hT] at hd
  by_cases ha : a ∈ T
  · right
    rcases bit_cases (s ⟨a,ha⟩) with hs | hs
    · refine ⟨ha,hs,?_⟩
      simp [signedSupport,ha,hs] at hd; omega
    · have hp := supportNegativeCount_pos T s ⟨a,ha⟩ (by simp [hs])
      simp [signedSupport,ha,hs] at hd; omega
  · left; refine ⟨ha,?_⟩
    simp [signedSupport,ha] at hd; omega

theorem co3_triangle_even_cases (a : Omega) (y : leech)
    (hy : integerDot y.val y.val = 32)
    (hd : integerDot (normSixVector a).val y.val = 8)
    (hp : ∀ i, y.val i % 2 = 0) :
    (∃ T : Finset Omega, T.card = 2 ∧ a ∉ T ∧ y.val = constantSupportVector 4 T) ∨
    (∃ T : Finset Omega, T ∈ octads ∧ ∃ s : T → Bit,
      y.val = (fun i => 2*signedSupport T s i) ∧
      ((a ∉ T ∧ supportNegativeCount T s = 2) ∨
        (∃ ha : a ∈ T, s ⟨a,ha⟩ = 0 ∧ supportNegativeCount T s = 4))) := by
  rw [integerDot_normSix] at hd
  rcases Finset.mem_union.mp ((even_minimal_shell_iff y.val).mp ⟨y.prop,hp,hy⟩) with h | h
  · obtain ⟨T,hT,s,hs⟩ := minimum_four_parameterization y h
    rw [hs] at hd
    obtain ⟨ha,hzero⟩ := co3_triangle_four_signs a T hT s hd
    refine Or.inl ⟨T,hT,ha,hs.trans ?_⟩
    funext i
    by_cases hi : i ∈ T <;> simp [signedSupport,constantSupportVector,hi,hzero]
  · obtain ⟨T,hT,hC,s,_,hs⟩ := minimum_octad_parameterization y h
    rw [hs] at hd
    exact Or.inr ⟨T,codeSupport_octad T hT hC,s,hs,co3_triangle_octad_signs a T hT s hd⟩

end Atlas.Conway
