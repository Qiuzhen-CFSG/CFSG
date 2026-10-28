/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeMinors

/-!
# HexacodeNormalForm

A normalized MDS graph matrix has the standard hexacode form, up to reversing its three-
cycle orientation. The minor constraints force its entries, and a coordinate swap
identifies the two orientations.

Source: `Atlas/Codes/HexacodeNormalForm.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def kleinNormalMatrix (P : KIsometry) : KleinMatrix := ![![1,1,1],![1,P,P⁻¹],![1,P⁻¹,P]]

theorem cycle_pair_inverse (P Q : KIsometry)
    (hP : P = localKappa ∨ P = localKappa⁻¹) (hQ : Q = localKappa ∨ Q = localKappa⁻¹)
    (hne : P ≠ Q) : Q = P⁻¹ := by
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl <;> simp_all

theorem normalized_matrix_forced (M : KleinMatrix) (hM : IsMDSMatrix M) :
    normalizedKleinMatrix M = kleinNormalMatrix (normalizedKleinMatrix M 1 1) := by
  have hP := normalized_coefficient_cycle M hM 1 1 (by decide) (by decide)
  have hQ := normalized_coefficient_cycle M hM 1 2 (by decide) (by decide)
  have hR := normalized_coefficient_cycle M hM 2 1 (by decide) (by decide)
  have hS := normalized_coefficient_cycle M hM 2 2 (by decide) (by decide)
  have hPQ := normalized_row_distinct M hM 1 1 2 (by decide) (by decide)
  have hPR := normalized_col_distinct M hM 1 2 1 (by decide) (by decide)
  have hRS := normalized_row_distinct M hM 2 1 2 (by decide) (by decide)
  have hq := cycle_pair_inverse _ _ hP hQ hPQ
  have hr := cycle_pair_inverse _ _ hP hR hPR
  have hs := cycle_pair_inverse _ _ hR hS hRS
  rw [hr,inv_inv] at hs
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [kleinNormalMatrix, hq,hr,hs]

def hexOrientationSwap : Monomial HexIndex where
  perm := Equiv.swap (lastThree 1) (lastThree 2)
  localMap _ := 1

theorem hexOrientationSwap_first : ∀ i : Fin 3,
    hexOrientationSwap.perm.symm (firstThree i) = firstThree i := by decide

theorem hexOrientationSwap_last : ∀ i : Fin 3,
    hexOrientationSwap.perm.symm (lastThree i) = lastThree (Equiv.swap 1 2 i) := by decide

theorem kleinGraph_orientation (P : KIsometry) (x : Fin 3 → K) :
    Monomial.act hexOrientationSwap (kleinGraphWord (kleinNormalMatrix P) x) =
      kleinGraphWord (kleinNormalMatrix P⁻¹) x := by
  funext p
  rcases hexIndex_first_or_last p with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · simp only [Monomial.act_apply,hexOrientationSwap_first]
    change kleinGraphWord (kleinNormalMatrix P) x (firstThree i) = _
    simp
  · simp only [Monomial.act_apply,hexOrientationSwap_last]
    change kleinGraphWord (kleinNormalMatrix P) x (lastThree (Equiv.swap 1 2 i)) = _
    rw [kleinGraphWord_last,kleinGraphWord_last]
    fin_cases i <;> simp [kleinNormalMatrix,Fin.sum_univ_succ,Equiv.swap_apply_def]

/-- The single auxiliary normal-form graph; it does not redefine the existing hexacode. -/
def KleinNormalWords : Set HexWord := Set.range (kleinGraphWord (kleinNormalMatrix localKappa))

theorem mds_graph_normal_form (M : KleinMatrix) (hM : IsMDSMatrix M) :
    ∃ g : Monomial HexIndex, ∀ w : HexWord,
      w ∈ Set.range (kleinGraphWord M) ↔ Monomial.act g w ∈ KleinNormalWords := by
  let N := normalizedKleinMatrix M
  have hN := normalized_matrix_forced M hM
  have hn : ∀ w, w ∈ Set.range (kleinGraphWord M) ↔
      Monomial.act (kleinNormalization M) w ∈ Set.range (kleinGraphWord N) := by
    intro w
    constructor
    · rintro ⟨x,rfl⟩
      refine ⟨fun j => M 0 j (x j),?_⟩
      rw [kleinGraph_normalization]
      simp
    · rintro ⟨x,hx⟩
      refine ⟨fun j => (M 0 j)⁻¹ (x j),?_⟩
      apply (Monomial.act (kleinNormalization M)).injective
      exact (kleinGraph_normalization M x).symm.trans hx
  rcases normalized_coefficient_cycle M hM 1 1 (by decide) (by decide) with h | h
  · refine ⟨kleinNormalization M,?_⟩
    intro w
    have he : N = kleinNormalMatrix localKappa := hN.trans (congrArg kleinNormalMatrix h)
    simpa only [he,KleinNormalWords] using hn w
  · refine ⟨hexOrientationSwap * kleinNormalization M,?_⟩
    intro w
    rw [hn,Monomial.act_mul]
    have he : N = kleinNormalMatrix localKappa⁻¹ := hN.trans (congrArg kleinNormalMatrix h)
    rw [he]
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨x,?_⟩
      rw [← hx,kleinGraph_orientation,inv_inv]
    · rintro ⟨x,hx⟩
      refine ⟨x,?_⟩
      apply (Monomial.act hexOrientationSwap).injective
      rw [kleinGraph_orientation,inv_inv]
      exact hx

end Atlas.Codes
