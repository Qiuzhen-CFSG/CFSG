/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeGraph

/-!
# HexacodeMinors

The MDS condition forces the two-by-two graph minors to have trivial kernels. In
normalized coordinates this makes the nontrivial coefficients fixed-point-free letter
permutations, restricting them to the two three-cycles and forcing row and column
distinctness.

Source: `Atlas/Codes/HexacodeMinors.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

theorem kleinGraphWord_single_last (M : KleinMatrix) (i j : Fin 3) (u : K) :
    kleinGraphWord M (Pi.single j u) (lastThree i) = M i j u := by
  rw [kleinGraphWord_last]
  simp [Pi.single_apply,apply_ite]

theorem kleinGraphWord_add (M : KleinMatrix) (x y : Fin 3 → K) :
    kleinGraphWord M (x+y) = kleinGraphWord M x + kleinGraphWord M y := by
  funext p
  rcases hexIndex_first_or_last p with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · simp
  · simp [map_add,Finset.sum_add_distrib]

theorem mds_minor_kernel (M : KleinMatrix) (hM : IsMDSMatrix M)
    (i k j l : Fin 3) (hik : i ≠ k) (hjl : j ≠ l) (u v : K)
    (hi : M i j u + M i l v = 0) (hk : M k j u + M k l v = 0) : u = 0 ∧ v = 0 := by
  have hex : ∀ j l : Fin 3, ∃ m : Fin 3, m ≠ j ∧ m ≠ l := by decide
  obtain ⟨m,hmj,hml⟩ := hex j l
  have hx := hM (Pi.single j u+Pi.single l v) (firstThree m) (lastThree i) (lastThree k)
    (firstThree_ne_lastThree m i) (firstThree_ne_lastThree m k) (lastThree.injective.ne hik)
    (by simp [hmj,hml])
    (by simpa only [kleinGraphWord_add,Pi.add_apply,kleinGraphWord_single_last] using hi)
    (by simpa only [kleinGraphWord_add,Pi.add_apply,kleinGraphWord_single_last] using hk)
  exact ⟨by simpa [Pi.single_apply,hjl,Ne.symm hjl] using congrFun hx j,
    by simpa [Pi.single_apply,hjl,Ne.symm hjl] using congrFun hx l⟩

theorem normalized_fixed_free (M : KleinMatrix) (hM : IsMDSMatrix M)
    (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) (u : K)
    (hu : normalizedKleinMatrix M i j u = u) : u = 0 := by
  have hh := mds_minor_kernel (normalizedKleinMatrix M) (normalizedKleinMatrix_valid M hM)
    0 i 0 j (Ne.symm hi) (Ne.symm hj) u u
    (by simp only [normalizedKleinMatrix_col,normalizedKleinMatrix_row,LinearEquiv.coe_one,id_eq]
        exact Prod.ext (bit_self_add _) (bit_self_add _))
    (by simpa only [normalizedKleinMatrix_col,LinearEquiv.coe_one, id_eq,hu] using
      (show u+u=0 from Prod.ext (bit_self_add _) (bit_self_add _)))
  exact hh.1

theorem kIsometry_fixed_free (L : KIsometry) (h : ∀ u, L u = u → u = 0) :
    L = localKappa ∨ L = localKappa⁻¹ := by
  rcases kIsometry_eq_six L with rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : a ≠ (0 : K)) (h a rfl))
  · exact False.elim ((by decide : a ≠ (0 : K)) (h a rfl))
  · exact False.elim ((by decide : c ≠ (0 : K)) (h c (by decide)))
  · exact False.elim ((by decide : b ≠ (0 : K)) (h b rfl))
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem normalized_coefficient_cycle (M : KleinMatrix) (hM : IsMDSMatrix M)
    (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
    normalizedKleinMatrix M i j = localKappa ∨ normalizedKleinMatrix M i j = localKappa⁻¹ :=
  kIsometry_fixed_free _ (normalized_fixed_free M hM i j hi hj)

theorem normalized_row_distinct (M : KleinMatrix) (hM : IsMDSMatrix M)
    (i j l : Fin 3) (hi : i ≠ 0) (hjl : j ≠ l) :
    normalizedKleinMatrix M i j ≠ normalizedKleinMatrix M i l := by
  intro he
  have ha : a+a=(0:K) := by decide
  have hz (L : KIsometry) : L a+L a=0 := by rw [← map_add,ha,map_zero]
  have hh := mds_minor_kernel (normalizedKleinMatrix M) (normalizedKleinMatrix_valid M hM)
    0 i j l (Ne.symm hi) hjl a a (by simpa using ha) (by rw [he]; exact hz _)
  exact (by decide : a ≠ (0:K)) hh.1

theorem normalized_col_distinct (M : KleinMatrix) (hM : IsMDSMatrix M)
    (i k j : Fin 3) (hik : i ≠ k) (hj : j ≠ 0) :
    normalizedKleinMatrix M i j ≠ normalizedKleinMatrix M k j := by
  intro he
  let v := normalizedKleinMatrix M i j a
  have hv : v+v=(0:K) := Prod.ext (bit_self_add _) (bit_self_add _)
  have hh := mds_minor_kernel (normalizedKleinMatrix M) (normalizedKleinMatrix_valid M hM)
    i k 0 j hik (Ne.symm hj) v a
    (by simpa only [normalizedKleinMatrix_col,LinearEquiv.coe_one, id_eq] using hv)
    (by rw [← he]; simpa only [normalizedKleinMatrix_col,LinearEquiv.coe_one, id_eq] using hv)
  exact (by decide : a ≠ (0:K)) hh.2

end Atlas.Codes
