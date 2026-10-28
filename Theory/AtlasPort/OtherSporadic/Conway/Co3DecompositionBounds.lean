/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3DecompositionBounds.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleBase
public import Theory.AtlasPort.OtherSporadic.Conway.MinimalEvenOrbits
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3DecompositionBounds.lean`, ATLAS revision
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

theorem integerDot_normSix (a : Omega) (y : IntegerCoordinates) :
    integerDot (normSixVector a).val y = (∑ i, y i) + 4*y a := by
  have hv : (normSixVector a).val = fun i => 1 + if i = a then 4 else 0 := by
    funext i; rw [normSixVector_apply]; split_ifs <;> norm_num
  rw [hv]
  simp [integerDot,add_mul,Finset.sum_add_distrib,ite_mul]

theorem normSix_decomposition_dot (a : Omega) (y : leech)
    (hy : integerDot y.val y.val = 32)
    (hz : integerDot (normSixVector a-y).val (normSixVector a-y).val = 32) :
    integerDot (normSixVector a).val y.val = 24 := by
  have he : integerDot (normSixVector a-y).val (normSixVector a-y).val =
      integerDot (normSixVector a).val (normSixVector a).val + integerDot y.val y.val -
        2*integerDot (normSixVector a).val y.val := by
    change (∑ i, ((normSixVector a).val i-y.val i)*((normSixVector a).val i-y.val i)) = _
    simp only [integerDot,Finset.mul_sum]
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [normSixVector_norm,hy,hz] at he
  omega

/-- Equality in the coordinate-sum bound forces every sign to be positive. -/
theorem signedSupport_sum_bound_eq (T : Finset Omega) (s : T → Bit) (a : Omega)
    (h : (∑ i, signedSupport T s i) + 4*signedSupport T s a = T.card + 4) :
    a ∈ T ∧ ∀ i : T, s i = 0 := by
  rw [signedSupport_sum] at h
  have hn : 0 ≤ ∑ i : T, (if s i = 0 then (0 : ℤ) else 1) :=
    Finset.sum_nonneg (fun i _ => by split_ifs <;> omega)
  have hb : signedSupport T s a ≤ 1 := by unfold signedSupport; split_ifs <;> omega
  have hz : (∑ i : T, (if s i = 0 then (0 : ℤ) else 1)) = 0 := by omega
  have ha : a ∈ T := by
    by_contra ha
    have hs : signedSupport T s a = 0 := by simp [signedSupport,ha]
    rw [hs] at h
    omega
  refine ⟨ha,?_⟩
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun (j : T) _ => show 0 ≤ (if s j = 0 then (0 : ℤ) else 1) by split_ifs <;> omega)).mp hz i (Finset.mem_univ i)
  split_ifs at hi with he
  · exact he
  · omega

theorem normSix_even_decomposition_positive (a : Omega) (y : leech)
    (hy : integerDot y.val y.val = 32)
    (hz : integerDot (normSixVector a-y).val (normSixVector a-y).val = 32)
    (hp : ∀ i, y.val i % 2 = 0) :
    (∃ T : Finset Omega, T.card = 2 ∧ a ∈ T ∧ y.val = constantSupportVector 4 T) ∨
    (∃ T : Finset Omega, T ∈ octads ∧ a ∈ T ∧ y.val = constantSupportVector 2 T) := by
  have hd := normSix_decomposition_dot a y hy hz
  rw [integerDot_normSix] at hd
  rcases Finset.mem_union.mp ((even_minimal_shell_iff y.val).mp ⟨y.prop,hp,hy⟩) with h | h
  · obtain ⟨T,hT,s,hs⟩ := minimum_four_parameterization y h
    rw [hs] at hd
    simp only [← Finset.mul_sum] at hd
    have he : (∑ i, signedSupport T s i) + 4*signedSupport T s a = T.card+4 := by
      norm_num only [hT,Nat.cast_ofNat]; linarith
    obtain ⟨ha,hzero⟩ := signedSupport_sum_bound_eq T s a he
    refine Or.inl ⟨T,hT,ha,hs.trans ?_⟩
    funext i
    by_cases hi : i ∈ T <;> simp [signedSupport,constantSupportVector,hi,hzero]
  · obtain ⟨T,hT,hC,s,_,hs⟩ := minimum_octad_parameterization y h
    rw [hs] at hd
    simp only [← Finset.mul_sum] at hd
    have he : (∑ i, signedSupport T s i) + 4*signedSupport T s a = T.card+4 := by
      norm_num only [hT,Nat.cast_ofNat]; linarith
    obtain ⟨ha,hzero⟩ := signedSupport_sum_bound_eq T s a he
    refine Or.inr ⟨T,codeSupport_octad T hT hC,ha,hs.trans ?_⟩
    funext i
    by_cases hi : i ∈ T <;> simp [signedSupport,constantSupportVector,hi,hzero]

end Atlas.Conway
