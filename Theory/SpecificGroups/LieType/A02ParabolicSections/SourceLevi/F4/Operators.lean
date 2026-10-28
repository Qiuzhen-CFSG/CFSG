module

public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Operators

/-!
# The two middle simple-root operators in the F4 adjoint lattice

The actual Cartan and root columns of the two middle Geck operators are
identified with explicit sparse integral matrices. Each column follows from
the root-sum formula, the negative-simple-root formula, or a checked root
exclusion. The only nonunit coefficient is the short-to-long root string.
Together with the existing end-root tables, these comparisons cover all four
simple roots, including their action on the full Cartan block.

Source: the integral Geck construction and the common lattice in GLS3 §1.12
and §2.6; used for the F4 Levi in Aschbacher–Smith A.2.18, printed p.40.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.Cartan.FieldSeparation.TraceValues ReeF4
namespace Theory.SpecificGroups.LieType.SourceLevi.F4.Operators
noncomputable section
open scoped Classical Matrix
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
private lemma root_simple_1 : root 30 = typeF4SimpleRootIndex 1 := by
  apply Subtype.ext
  ext q
  fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
def positive1Linear : Sparse :=
  [(1,33,1), (9,11,1), (10,8,1), (17,21,1), (19,23,1), (20,16,1), (22,18,1), (25,29,1), (27,31,1), (28,24,1), (30,26,1), (34,0,1), (34,1,2), (34,2,2), (38,37,1), (42,41,1), (46,45,1), (50,49,1)]
private def columns1 (c : Fin 52) : Fin 52 × ℤ :=
  (![(34,1), (34,2), (34,2), (0,0), (0,0), (0,0), (0,0), (0,0), (10,1), (0,0), (0,0), (9,1), (0,0), (0,0), (0,0), (0,0), (20,1), (0,0), (22,1), (0,0), (0,0), (17,1), (0,0), (19,1), (28,1), (0,0), (30,1), (0,0), (0,0), (25,1), (0,0), (27,1), (0,0), (1,1), (0,0), (0,0), (0,0), (38,1), (0,0), (0,0), (0,0), (42,1), (0,0), (0,0), (0,0), (46,1), (0,0), (0,0), (0,0), (50,1), (0,0), (0,0)]) c
private lemma table_columns1 (c : Fin 52) :
    matrix positive1Linear *ᵥ Pi.single c 1 =
      (columns1 c).2 • Pi.single (columns1 c).1 1 := by
  simp only [Matrix.mulVec_single_one]
  revert c
  decide +kernel
private lemma eMatrix_1_column_0 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (0 : Fin 52) 1 = (1 : ℤ) • Pi.single (34 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    u (typeF4RootPairing_baseEquiv 0) = (1 : ℤ) • v (root 30)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_1]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]
private lemma eMatrix_1_column_1 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (1 : Fin 52) 1 = (2 : ℤ) • Pi.single (34 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    u (typeF4RootPairing_baseEquiv 1) = (2 : ℤ) • v (root 30)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_1]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]
private lemma eMatrix_1_column_2 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (2 : Fin 52) 1 = (2 : ℤ) • Pi.single (34 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    u (typeF4RootPairing_baseEquiv 2) = (2 : ℤ) • v (root 30)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_1]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]
private lemma eMatrix_1_column_3 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (3 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ u (typeF4RootPairing_baseEquiv 3) = 0
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]
private lemma eMatrix_1_column_4 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (4 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 0) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_5 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (5 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 1) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_6 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (6 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 2) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_7 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (7 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 3) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_8 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (8 : Fin 52) 1 = (1 : ℤ) • Pi.single (10 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 4) = (1 : ℤ) • v (root 6)
  have hs : typeF4RootPairing.root (root 6) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 4) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 4)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_9 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (9 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 5) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 2) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_10 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (10 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 6) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 2) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_11 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (11 : Fin 52) 1 = (1 : ℤ) • Pi.single (9 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 7) = (1 : ℤ) • v (root 5)
  have hs : typeF4RootPairing.root (root 5) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 7) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 7)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_12 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (12 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 8) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_13 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (13 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 9) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_14 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (14 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 10) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_15 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (15 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 11) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_16 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (16 : Fin 52) 1 = (1 : ℤ) • Pi.single (20 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 12) = (1 : ℤ) • v (root 16)
  have hs : typeF4RootPairing.root (root 16) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 12) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 12)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_17 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (17 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 13) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_18 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (18 : Fin 52) 1 = (1 : ℤ) • Pi.single (22 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 14) = (1 : ℤ) • v (root 18)
  have hs : typeF4RootPairing.root (root 18) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 14) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 14)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_19 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (19 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 15) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_20 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (20 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 16) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_21 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (21 : Fin 52) 1 = (1 : ℤ) • Pi.single (17 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 17) = (1 : ℤ) • v (root 13)
  have hs : typeF4RootPairing.root (root 13) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 17) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 17)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_22 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (22 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 18) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_23 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (23 : Fin 52) 1 = (1 : ℤ) • Pi.single (19 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 19) = (1 : ℤ) • v (root 15)
  have hs : typeF4RootPairing.root (root 15) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 19) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 19)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_24 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (24 : Fin 52) 1 = (1 : ℤ) • Pi.single (28 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 20) = (1 : ℤ) • v (root 24)
  have hs : typeF4RootPairing.root (root 24) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 20) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 20)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_25 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (25 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 21) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_26 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (26 : Fin 52) 1 = (1 : ℤ) • Pi.single (30 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 22) = (1 : ℤ) • v (root 26)
  have hs : typeF4RootPairing.root (root 26) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 22) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 22)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_27 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (27 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 23) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_28 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (28 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 24) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_29 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (29 : Fin 52) 1 = (1 : ℤ) • Pi.single (25 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 25) = (1 : ℤ) • v (root 21)
  have hs : typeF4RootPairing.root (root 21) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 25) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 25)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_30 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (30 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 26) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_31 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (31 : Fin 52) 1 = (1 : ℤ) • Pi.single (27 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 27) = (1 : ℤ) • v (root 23)
  have hs : typeF4RootPairing.root (root 23) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 27) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 27)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_32 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (32 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 28) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 3) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_33 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (33 : Fin 52) 1 = (1 : ℤ) • Pi.single (1 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 29) = (1 : ℤ) • u (typeF4RootPairing_baseEquiv 1)
  have hn : root 29 = -(typeF4RootPairing_baseEquiv 1).val := by
    apply typeF4RootPairing.root.injective
    rw [root_neg_value]
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [hn, eMatrix_mulVec_v_neg, one_smul]
private lemma eMatrix_1_column_34 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (34 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 30) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 2) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_35 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (35 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 31) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 2) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_36 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (36 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 32) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_37 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (37 : Fin 52) 1 = (1 : ℤ) • Pi.single (38 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 33) = (1 : ℤ) • v (root 34)
  have hs : typeF4RootPairing.root (root 34) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 33) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 33)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_38 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (38 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 34) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_39 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (39 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 35) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_40 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (40 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 36) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_41 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (41 : Fin 52) 1 = (1 : ℤ) • Pi.single (42 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 37) = (1 : ℤ) • v (root 38)
  have hs : typeF4RootPairing.root (root 38) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 37) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 37)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_42 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (42 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 38) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_43 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (43 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 39) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_44 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (44 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 40) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_45 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (45 : Fin 52) 1 = (1 : ℤ) • Pi.single (46 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 41) = (1 : ℤ) • v (root 42)
  have hs : typeF4RootPairing.root (root 42) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 41) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 41)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_46 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (46 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 42) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_47 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (47 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 43) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_48 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (48 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 44) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_49 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (49 : Fin 52) 1 = (1 : ℤ) • Pi.single (50 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    v (root 45) = (1 : ℤ) • v (root 46)
  have hs : typeF4RootPairing.root (root 46) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 45) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 45)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_1_column_50 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (50 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 46) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_1_column_51 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (51 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 47) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
theorem eMatrix_1 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) = matrix positive1Linear := by
  apply Matrix.ext_col
  intro c
  rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_single_one, table_columns1]
  fin_cases c
  · exact eMatrix_1_column_0
  · exact eMatrix_1_column_1
  · exact eMatrix_1_column_2
  · exact eMatrix_1_column_3
  · exact eMatrix_1_column_4
  · exact eMatrix_1_column_5
  · exact eMatrix_1_column_6
  · exact eMatrix_1_column_7
  · exact eMatrix_1_column_8
  · exact eMatrix_1_column_9
  · exact eMatrix_1_column_10
  · exact eMatrix_1_column_11
  · exact eMatrix_1_column_12
  · exact eMatrix_1_column_13
  · exact eMatrix_1_column_14
  · exact eMatrix_1_column_15
  · exact eMatrix_1_column_16
  · exact eMatrix_1_column_17
  · exact eMatrix_1_column_18
  · exact eMatrix_1_column_19
  · exact eMatrix_1_column_20
  · exact eMatrix_1_column_21
  · exact eMatrix_1_column_22
  · exact eMatrix_1_column_23
  · exact eMatrix_1_column_24
  · exact eMatrix_1_column_25
  · exact eMatrix_1_column_26
  · exact eMatrix_1_column_27
  · exact eMatrix_1_column_28
  · exact eMatrix_1_column_29
  · exact eMatrix_1_column_30
  · exact eMatrix_1_column_31
  · exact eMatrix_1_column_32
  · exact eMatrix_1_column_33
  · exact eMatrix_1_column_34
  · exact eMatrix_1_column_35
  · exact eMatrix_1_column_36
  · exact eMatrix_1_column_37
  · exact eMatrix_1_column_38
  · exact eMatrix_1_column_39
  · exact eMatrix_1_column_40
  · exact eMatrix_1_column_41
  · exact eMatrix_1_column_42
  · exact eMatrix_1_column_43
  · exact eMatrix_1_column_44
  · exact eMatrix_1_column_45
  · exact eMatrix_1_column_46
  · exact eMatrix_1_column_47
  · exact eMatrix_1_column_48
  · exact eMatrix_1_column_49
  · exact eMatrix_1_column_50
  · exact eMatrix_1_column_51
private lemma root_simple_2 : root 7 = typeF4SimpleRootIndex 2 := by
  apply Subtype.ext
  ext q
  fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
def positive2Linear : Sparse :=
  [(2,10,1), (4,20,1), (5,22,1), (6,28,1), (7,30,1), (8,32,1), (9,34,1), (11,1,1), (11,2,2), (11,3,1), (21,4,2), (23,5,2), (29,6,2), (31,7,2), (33,8,2), (35,9,2), (37,36,1), (39,38,1), (41,40,1), (43,42,1), (45,44,1), (47,46,1), (49,48,1), (51,50,1)]
private def columns2 (c : Fin 52) : Fin 52 × ℤ :=
  (![(0,0), (11,1), (11,2), (11,1), (21,2), (23,2), (29,2), (31,2), (33,2), (35,2), (2,1), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (4,1), (0,0), (5,1), (0,0), (0,0), (0,0), (0,0), (0,0), (6,1), (0,0), (7,1), (0,0), (8,1), (0,0), (9,1), (0,0), (37,1), (0,0), (39,1), (0,0), (41,1), (0,0), (43,1), (0,0), (45,1), (0,0), (47,1), (0,0), (49,1), (0,0), (51,1), (0,0)]) c
private lemma table_columns2 (c : Fin 52) :
    matrix positive2Linear *ᵥ Pi.single c 1 =
      (columns2 c).2 • Pi.single (columns2 c).1 1 := by
  simp only [Matrix.mulVec_single_one]
  revert c
  decide +kernel
private lemma eMatrix_2_column_0 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (0 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ u (typeF4RootPairing_baseEquiv 0) = 0
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]
private lemma eMatrix_2_column_1 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (1 : Fin 52) 1 = (1 : ℤ) • Pi.single (11 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    u (typeF4RootPairing_baseEquiv 1) = (1 : ℤ) • v (root 7)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_2]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]
private lemma eMatrix_2_column_2 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (2 : Fin 52) 1 = (2 : ℤ) • Pi.single (11 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    u (typeF4RootPairing_baseEquiv 2) = (2 : ℤ) • v (root 7)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_2]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]
private lemma eMatrix_2_column_3 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (3 : Fin 52) 1 = (1 : ℤ) • Pi.single (11 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    u (typeF4RootPairing_baseEquiv 3) = (1 : ℤ) • v (root 7)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_2]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]
private lemma eMatrix_2_column_4 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (4 : Fin 52) 1 = (2 : ℤ) • Pi.single (21 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 0) = (2 : ℤ) • v (root 17)
  have hs : typeF4RootPairing.root (root 17) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 0) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 2).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 2)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 17) := by
    by_contra hn
    have hh := isShortRoot_norm (root 17) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [ReeF4.WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num
private lemma eMatrix_2_column_5 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (5 : Fin 52) 1 = (2 : ℤ) • Pi.single (23 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 1) = (2 : ℤ) • v (root 19)
  have hs : typeF4RootPairing.root (root 19) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 1) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 2).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 2)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 19) := by
    by_contra hn
    have hh := isShortRoot_norm (root 19) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [ReeF4.WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num
private lemma eMatrix_2_column_6 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (6 : Fin 52) 1 = (2 : ℤ) • Pi.single (29 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 2) = (2 : ℤ) • v (root 25)
  have hs : typeF4RootPairing.root (root 25) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 2) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 2).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 2)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 25) := by
    by_contra hn
    have hh := isShortRoot_norm (root 25) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [ReeF4.WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num
private lemma eMatrix_2_column_7 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (7 : Fin 52) 1 = (2 : ℤ) • Pi.single (31 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 3) = (2 : ℤ) • v (root 27)
  have hs : typeF4RootPairing.root (root 27) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 3) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 2).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 2)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 27) := by
    by_contra hn
    have hh := isShortRoot_norm (root 27) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [ReeF4.WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num
private lemma eMatrix_2_column_8 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (8 : Fin 52) 1 = (2 : ℤ) • Pi.single (33 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 4) = (2 : ℤ) • v (root 29)
  have hs : typeF4RootPairing.root (root 29) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 4) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 2).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 2)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 29) := by
    by_contra hn
    have hh := isShortRoot_norm (root 29) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [ReeF4.WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num
private lemma eMatrix_2_column_9 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (9 : Fin 52) 1 = (2 : ℤ) • Pi.single (35 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 5) = (2 : ℤ) • v (root 31)
  have hs : typeF4RootPairing.root (root 31) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 5) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 2).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 2)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 31) := by
    by_contra hn
    have hh := isShortRoot_norm (root 31) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [ReeF4.WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num
private lemma eMatrix_2_column_10 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (10 : Fin 52) 1 = (1 : ℤ) • Pi.single (2 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 6) = (1 : ℤ) • u (typeF4RootPairing_baseEquiv 2)
  have hn : root 6 = -(typeF4RootPairing_baseEquiv 2).val := by
    apply typeF4RootPairing.root.injective
    rw [root_neg_value]
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [hn, eMatrix_mulVec_v_neg, one_smul]
private lemma eMatrix_2_column_11 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (11 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 7) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 3) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_12 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (12 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 8) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_13 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (13 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 9) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_14 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (14 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 10) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_15 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (15 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 11) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_16 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (16 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 12) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_17 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (17 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 13) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_18 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (18 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 14) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_19 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (19 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 15) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_20 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (20 : Fin 52) 1 = (1 : ℤ) • Pi.single (4 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 16) = (1 : ℤ) • v (root 0)
  have hs : typeF4RootPairing.root (root 0) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 16) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 16)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_21 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (21 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 17) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_22 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (22 : Fin 52) 1 = (1 : ℤ) • Pi.single (5 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 18) = (1 : ℤ) • v (root 1)
  have hs : typeF4RootPairing.root (root 1) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 18) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 18)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_23 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (23 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 19) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_24 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (24 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 20) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_25 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (25 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 21) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_26 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (26 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 22) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_27 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (27 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 23) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_28 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (28 : Fin 52) 1 = (1 : ℤ) • Pi.single (6 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 24) = (1 : ℤ) • v (root 2)
  have hs : typeF4RootPairing.root (root 2) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 24) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 24)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_29 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (29 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 25) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_30 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (30 : Fin 52) 1 = (1 : ℤ) • Pi.single (7 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 26) = (1 : ℤ) • v (root 3)
  have hs : typeF4RootPairing.root (root 3) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 26) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 26)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_31 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (31 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 27) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_32 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (32 : Fin 52) 1 = (1 : ℤ) • Pi.single (8 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 28) = (1 : ℤ) • v (root 4)
  have hs : typeF4RootPairing.root (root 4) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 28) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 28)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_33 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (33 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 29) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 2) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_34 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (34 : Fin 52) 1 = (1 : ℤ) • Pi.single (9 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 30) = (1 : ℤ) • v (root 5)
  have hs : typeF4RootPairing.root (root 5) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 30) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 30)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_35 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (35 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 31) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 2) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_36 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (36 : Fin 52) 1 = (1 : ℤ) • Pi.single (37 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 32) = (1 : ℤ) • v (root 33)
  have hs : typeF4RootPairing.root (root 33) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 32) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 32)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_37 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (37 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 33) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_38 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (38 : Fin 52) 1 = (1 : ℤ) • Pi.single (39 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 34) = (1 : ℤ) • v (root 35)
  have hs : typeF4RootPairing.root (root 35) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 34) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 34)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_39 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (39 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 35) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_40 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (40 : Fin 52) 1 = (1 : ℤ) • Pi.single (41 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 36) = (1 : ℤ) • v (root 37)
  have hs : typeF4RootPairing.root (root 37) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 36) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 36)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_41 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (41 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 37) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_42 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (42 : Fin 52) 1 = (1 : ℤ) • Pi.single (43 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 38) = (1 : ℤ) • v (root 39)
  have hs : typeF4RootPairing.root (root 39) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 38) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 38)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_43 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (43 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 39) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_44 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (44 : Fin 52) 1 = (1 : ℤ) • Pi.single (45 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 40) = (1 : ℤ) • v (root 41)
  have hs : typeF4RootPairing.root (root 41) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 40) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 40)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_45 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (45 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 41) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_46 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (46 : Fin 52) 1 = (1 : ℤ) • Pi.single (47 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 42) = (1 : ℤ) • v (root 43)
  have hs : typeF4RootPairing.root (root 43) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 42) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 42)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_47 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (47 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 43) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_48 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (48 : Fin 52) 1 = (1 : ℤ) • Pi.single (49 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 44) = (1 : ℤ) • v (root 45)
  have hs : typeF4RootPairing.root (root 45) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 44) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 44)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_49 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (49 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 45) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
private lemma eMatrix_2_column_50 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (50 : Fin 52) 1 = (1 : ℤ) • Pi.single (51 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    v (root 46) = (1 : ℤ) • v (root 47)
  have hs : typeF4RootPairing.root (root 47) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 46) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 46)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num
private lemma eMatrix_2_column_51 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (51 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 47) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
theorem eMatrix_2 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) = matrix positive2Linear := by
  apply Matrix.ext_col
  intro c
  rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_single_one, table_columns2]
  fin_cases c
  · exact eMatrix_2_column_0
  · exact eMatrix_2_column_1
  · exact eMatrix_2_column_2
  · exact eMatrix_2_column_3
  · exact eMatrix_2_column_4
  · exact eMatrix_2_column_5
  · exact eMatrix_2_column_6
  · exact eMatrix_2_column_7
  · exact eMatrix_2_column_8
  · exact eMatrix_2_column_9
  · exact eMatrix_2_column_10
  · exact eMatrix_2_column_11
  · exact eMatrix_2_column_12
  · exact eMatrix_2_column_13
  · exact eMatrix_2_column_14
  · exact eMatrix_2_column_15
  · exact eMatrix_2_column_16
  · exact eMatrix_2_column_17
  · exact eMatrix_2_column_18
  · exact eMatrix_2_column_19
  · exact eMatrix_2_column_20
  · exact eMatrix_2_column_21
  · exact eMatrix_2_column_22
  · exact eMatrix_2_column_23
  · exact eMatrix_2_column_24
  · exact eMatrix_2_column_25
  · exact eMatrix_2_column_26
  · exact eMatrix_2_column_27
  · exact eMatrix_2_column_28
  · exact eMatrix_2_column_29
  · exact eMatrix_2_column_30
  · exact eMatrix_2_column_31
  · exact eMatrix_2_column_32
  · exact eMatrix_2_column_33
  · exact eMatrix_2_column_34
  · exact eMatrix_2_column_35
  · exact eMatrix_2_column_36
  · exact eMatrix_2_column_37
  · exact eMatrix_2_column_38
  · exact eMatrix_2_column_39
  · exact eMatrix_2_column_40
  · exact eMatrix_2_column_41
  · exact eMatrix_2_column_42
  · exact eMatrix_2_column_43
  · exact eMatrix_2_column_44
  · exact eMatrix_2_column_45
  · exact eMatrix_2_column_46
  · exact eMatrix_2_column_47
  · exact eMatrix_2_column_48
  · exact eMatrix_2_column_49
  · exact eMatrix_2_column_50
  · exact eMatrix_2_column_51
end
end Theory.SpecificGroups.LieType.SourceLevi.F4.Operators
