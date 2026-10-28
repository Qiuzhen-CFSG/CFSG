module
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Operators
/-!
# The middle simple-root matrices

Column formulas for the actual integral Geck operators certify the two middle
simple-root tables. Root sums and squared Euclidean lengths determine the
root columns. These tables supplement the end-root tables in `TraceValues.Operators`.
Source: Geck's integral construction, GLS3 §1.12 and §2.6.
-/
@[expose] public section
namespace ReeF4.SectionGeometry.LinearRadical.LeviDetection.RootCentralizer
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.Cartan.FieldSeparation.TraceValues
noncomputable section
open scoped Classical Matrix
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

def middleColumns1 : Fin 52 → Fin 52 × ℤ :=
  ![(34, 1), (34, 2), (34, 2), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (10, 1), (0, 0), (0, 0), (9, 1), (0, 0), (0, 0), (0, 0), (0, 0), (20, 1), (0, 0), (22, 1), (0, 0), (0, 0), (17, 1), (0, 0), (19, 1), (28, 1), (0, 0), (30, 1), (0, 0), (0, 0), (25, 1), (0, 0), (27, 1), (0, 0), (1, 1), (0, 0), (0, 0), (0, 0), (38, 1), (0, 0), (0, 0), (0, 0), (42, 1), (0, 0), (0, 0), (0, 0), (46, 1), (0, 0), (0, 0), (0, 0), (50, 1), (0, 0), (0, 0)]

def middleTable1 : Matrix (Fin 52) (Fin 52) ℤ :=
  fun i j => if i = (middleColumns1 j).1 then (middleColumns1 j).2 else 0

private lemma middleTable1_column (c : Fin 52) :
    middleTable1 *ᵥ Pi.single c 1 =
      (middleColumns1 c).2 • Pi.single (middleColumns1 c).1 1 := by
  ext i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, middleTable1,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma middleSimple1 : root 30 = typeF4SimpleRootIndex 1 := by
  apply Subtype.ext
  ext q
  fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_0 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (0 : Fin 52) 1 = (1 : ℤ) • Pi.single (34 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    u (typeF4RootPairing_baseEquiv 0) = (1 : ℤ) • v (root 30)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  rw [typeF4RootPairing_baseEquiv_val, ← middleSimple1]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma middle1_column_1 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (1 : Fin 52) 1 = (2 : ℤ) • Pi.single (34 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    u (typeF4RootPairing_baseEquiv 1) = (2 : ℤ) • v (root 30)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  rw [typeF4RootPairing_baseEquiv_val, ← middleSimple1]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma middle1_column_2 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (2 : Fin 52) 1 = (2 : ℤ) • Pi.single (34 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    u (typeF4RootPairing_baseEquiv 2) = (2 : ℤ) • v (root 30)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  rw [typeF4RootPairing_baseEquiv_val, ← middleSimple1]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma middle1_column_3 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (3 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ
    u (typeF4RootPairing_baseEquiv 3) = (0 : ℤ) • u (typeF4RootPairing_baseEquiv 0)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma middle1_column_4 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_5 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_6 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_7 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_8 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (8 : Fin 52) 1 = (1 : ℤ) • Pi.single (10 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 4) =
    (1 : ℤ) • v (root 6)
  have hs : typeF4RootPairing.root (root 6) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 4) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 4)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_9 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_10 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_11 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (11 : Fin 52) 1 = (1 : ℤ) • Pi.single (9 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 7) =
    (1 : ℤ) • v (root 5)
  have hs : typeF4RootPairing.root (root 5) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 7) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 7)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_12 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_13 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_14 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_15 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_16 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (16 : Fin 52) 1 = (1 : ℤ) • Pi.single (20 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 12) =
    (1 : ℤ) • v (root 16)
  have hs : typeF4RootPairing.root (root 16) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 12) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 12)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_17 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_18 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (18 : Fin 52) 1 = (1 : ℤ) • Pi.single (22 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 14) =
    (1 : ℤ) • v (root 18)
  have hs : typeF4RootPairing.root (root 18) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 14) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 14)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_19 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_20 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_21 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (21 : Fin 52) 1 = (1 : ℤ) • Pi.single (17 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 17) =
    (1 : ℤ) • v (root 13)
  have hs : typeF4RootPairing.root (root 13) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 17) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 17)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_22 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_23 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (23 : Fin 52) 1 = (1 : ℤ) • Pi.single (19 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 19) =
    (1 : ℤ) • v (root 15)
  have hs : typeF4RootPairing.root (root 15) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 19) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 19)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_24 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (24 : Fin 52) 1 = (1 : ℤ) • Pi.single (28 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 20) =
    (1 : ℤ) • v (root 24)
  have hs : typeF4RootPairing.root (root 24) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 20) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 20)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_25 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_26 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (26 : Fin 52) 1 = (1 : ℤ) • Pi.single (30 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 22) =
    (1 : ℤ) • v (root 26)
  have hs : typeF4RootPairing.root (root 26) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 22) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 22)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_27 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_28 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_29 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (29 : Fin 52) 1 = (1 : ℤ) • Pi.single (25 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 25) =
    (1 : ℤ) • v (root 21)
  have hs : typeF4RootPairing.root (root 21) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 25) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 25)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_30 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_31 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (31 : Fin 52) 1 = (1 : ℤ) • Pi.single (27 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 27) =
    (1 : ℤ) • v (root 23)
  have hs : typeF4RootPairing.root (root 23) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 27) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 27)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_32 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_33 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (33 : Fin 52) 1 = (1 : ℤ) • Pi.single (1 : Fin 52) 1 := by
  apply reindex_column
  have hn : root 29 = -(typeF4RootPairing_baseEquiv 1 : typeF4Roots) := by
    apply typeF4RootPairing.root.injective
    rw [root_neg_value]
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 29) =
    (1 : ℤ) • u (typeF4RootPairing_baseEquiv 1)
  rw [hn, eMatrix_mulVec_v_neg, one_smul]

private lemma middle1_column_34 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_35 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_36 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_37 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (37 : Fin 52) 1 = (1 : ℤ) • Pi.single (38 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 33) =
    (1 : ℤ) • v (root 34)
  have hs : typeF4RootPairing.root (root 34) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 33) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 33)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_38 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_39 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_40 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_41 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (41 : Fin 52) 1 = (1 : ℤ) • Pi.single (42 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 37) =
    (1 : ℤ) • v (root 38)
  have hs : typeF4RootPairing.root (root 38) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 37) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 37)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_42 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_43 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_44 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_45 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (45 : Fin 52) 1 = (1 : ℤ) • Pi.single (46 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 41) =
    (1 : ℤ) • v (root 42)
  have hs : typeF4RootPairing.root (root 42) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 41) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 41)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_46 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_47 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_48 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_49 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single (49 : Fin 52) 1 = (1 : ℤ) • Pi.single (50 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 1) *ᵥ v (root 45) =
    (1 : ℤ) • v (root 46)
  have hs : typeF4RootPairing.root (root 46) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) +
      typeF4RootPairing.root (root 45) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 1) (root 45)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle1_column_50 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle1_column_51 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

/-- The actual middle simple-root operator, in the numbered lattice basis. -/
lemma reindex_middle1 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) = middleTable1 := by
  have hc (c : Fin 52) : reindex (eMatrix (typeF4RootPairing_baseEquiv 1)) *ᵥ
      Pi.single c 1 = middleTable1 *ᵥ Pi.single c 1 := by
    rw [middleTable1_column]
    fin_cases c
    · exact middle1_column_0
    · exact middle1_column_1
    · exact middle1_column_2
    · exact middle1_column_3
    · exact middle1_column_4
    · exact middle1_column_5
    · exact middle1_column_6
    · exact middle1_column_7
    · exact middle1_column_8
    · exact middle1_column_9
    · exact middle1_column_10
    · exact middle1_column_11
    · exact middle1_column_12
    · exact middle1_column_13
    · exact middle1_column_14
    · exact middle1_column_15
    · exact middle1_column_16
    · exact middle1_column_17
    · exact middle1_column_18
    · exact middle1_column_19
    · exact middle1_column_20
    · exact middle1_column_21
    · exact middle1_column_22
    · exact middle1_column_23
    · exact middle1_column_24
    · exact middle1_column_25
    · exact middle1_column_26
    · exact middle1_column_27
    · exact middle1_column_28
    · exact middle1_column_29
    · exact middle1_column_30
    · exact middle1_column_31
    · exact middle1_column_32
    · exact middle1_column_33
    · exact middle1_column_34
    · exact middle1_column_35
    · exact middle1_column_36
    · exact middle1_column_37
    · exact middle1_column_38
    · exact middle1_column_39
    · exact middle1_column_40
    · exact middle1_column_41
    · exact middle1_column_42
    · exact middle1_column_43
    · exact middle1_column_44
    · exact middle1_column_45
    · exact middle1_column_46
    · exact middle1_column_47
    · exact middle1_column_48
    · exact middle1_column_49
    · exact middle1_column_50
    · exact middle1_column_51
  ext i j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hc j) i

def middleColumns2 : Fin 52 → Fin 52 × ℤ :=
  ![(0, 0), (11, 1), (11, 2), (11, 1), (21, 2), (23, 2), (29, 2), (31, 2), (33, 2), (35, 2), (2, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (4, 1), (0, 0), (5, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (6, 1), (0, 0), (7, 1), (0, 0), (8, 1), (0, 0), (9, 1), (0, 0), (37, 1), (0, 0), (39, 1), (0, 0), (41, 1), (0, 0), (43, 1), (0, 0), (45, 1), (0, 0), (47, 1), (0, 0), (49, 1), (0, 0), (51, 1), (0, 0)]

def middleTable2 : Matrix (Fin 52) (Fin 52) ℤ :=
  fun i j => if i = (middleColumns2 j).1 then (middleColumns2 j).2 else 0

private lemma middleTable2_column (c : Fin 52) :
    middleTable2 *ᵥ Pi.single c 1 =
      (middleColumns2 c).2 • Pi.single (middleColumns2 c).1 1 := by
  ext i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, middleTable2,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma middleSimple2 : root 7 = typeF4SimpleRootIndex 2 := by
  apply Subtype.ext
  ext q
  fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_0 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (0 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    u (typeF4RootPairing_baseEquiv 0) = (0 : ℤ) • u (typeF4RootPairing_baseEquiv 0)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma middle2_column_1 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (1 : Fin 52) 1 = (1 : ℤ) • Pi.single (11 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    u (typeF4RootPairing_baseEquiv 1) = (1 : ℤ) • v (root 7)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  rw [typeF4RootPairing_baseEquiv_val, ← middleSimple2]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma middle2_column_2 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (2 : Fin 52) 1 = (2 : ℤ) • Pi.single (11 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    u (typeF4RootPairing_baseEquiv 2) = (2 : ℤ) • v (root 7)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  rw [typeF4RootPairing_baseEquiv_val, ← middleSimple2]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma middle2_column_3 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (3 : Fin 52) 1 = (1 : ℤ) • Pi.single (11 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ
    u (typeF4RootPairing_baseEquiv 3) = (1 : ℤ) • v (root 7)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  rw [typeF4RootPairing_baseEquiv_val, ← middleSimple2]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma middle2_column_4 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (4 : Fin 52) 1 = (2 : ℤ) • Pi.single (21 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 0) =
    (2 : ℤ) • v (root 17)
  have hs : typeF4RootPairing.root (root 17) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 0) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := ReeF4.WordRelations.chainBotCoeff_short_add_long
    (i := (typeF4RootPairing_baseEquiv 2 : typeF4Roots)) (j := root 0)
    (k := root 17)
    (by intro h; have hh := isLongRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh)
    (by by_contra h; have hh := isShortRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh) hs
  rw [hb]
  norm_num

private lemma middle2_column_5 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (5 : Fin 52) 1 = (2 : ℤ) • Pi.single (23 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 1) =
    (2 : ℤ) • v (root 19)
  have hs : typeF4RootPairing.root (root 19) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 1) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := ReeF4.WordRelations.chainBotCoeff_short_add_long
    (i := (typeF4RootPairing_baseEquiv 2 : typeF4Roots)) (j := root 1)
    (k := root 19)
    (by intro h; have hh := isLongRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh)
    (by by_contra h; have hh := isShortRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh) hs
  rw [hb]
  norm_num

private lemma middle2_column_6 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (6 : Fin 52) 1 = (2 : ℤ) • Pi.single (29 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 2) =
    (2 : ℤ) • v (root 25)
  have hs : typeF4RootPairing.root (root 25) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 2) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := ReeF4.WordRelations.chainBotCoeff_short_add_long
    (i := (typeF4RootPairing_baseEquiv 2 : typeF4Roots)) (j := root 2)
    (k := root 25)
    (by intro h; have hh := isLongRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh)
    (by by_contra h; have hh := isShortRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh) hs
  rw [hb]
  norm_num

private lemma middle2_column_7 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (7 : Fin 52) 1 = (2 : ℤ) • Pi.single (31 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 3) =
    (2 : ℤ) • v (root 27)
  have hs : typeF4RootPairing.root (root 27) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 3) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := ReeF4.WordRelations.chainBotCoeff_short_add_long
    (i := (typeF4RootPairing_baseEquiv 2 : typeF4Roots)) (j := root 3)
    (k := root 27)
    (by intro h; have hh := isLongRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh)
    (by by_contra h; have hh := isShortRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh) hs
  rw [hb]
  norm_num

private lemma middle2_column_8 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (8 : Fin 52) 1 = (2 : ℤ) • Pi.single (33 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 4) =
    (2 : ℤ) • v (root 29)
  have hs : typeF4RootPairing.root (root 29) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 4) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := ReeF4.WordRelations.chainBotCoeff_short_add_long
    (i := (typeF4RootPairing_baseEquiv 2 : typeF4Roots)) (j := root 4)
    (k := root 29)
    (by intro h; have hh := isLongRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh)
    (by by_contra h; have hh := isShortRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh) hs
  rw [hb]
  norm_num

private lemma middle2_column_9 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (9 : Fin 52) 1 = (2 : ℤ) • Pi.single (35 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 5) =
    (2 : ℤ) • v (root 31)
  have hs : typeF4RootPairing.root (root 31) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 5) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := ReeF4.WordRelations.chainBotCoeff_short_add_long
    (i := (typeF4RootPairing_baseEquiv 2 : typeF4Roots)) (j := root 5)
    (k := root 31)
    (by intro h; have hh := isLongRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh)
    (by by_contra h; have hh := isShortRoot_norm _ h; norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh) hs
  rw [hb]
  norm_num

private lemma middle2_column_10 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (10 : Fin 52) 1 = (1 : ℤ) • Pi.single (2 : Fin 52) 1 := by
  apply reindex_column
  have hn : root 6 = -(typeF4RootPairing_baseEquiv 2 : typeF4Roots) := by
    apply typeF4RootPairing.root.injective
    rw [root_neg_value]
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 6) =
    (1 : ℤ) • u (typeF4RootPairing_baseEquiv 2)
  rw [hn, eMatrix_mulVec_v_neg, one_smul]

private lemma middle2_column_11 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_12 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_13 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_14 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_15 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_16 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_17 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_18 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_19 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_20 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (20 : Fin 52) 1 = (1 : ℤ) • Pi.single (4 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 16) =
    (1 : ℤ) • v (root 0)
  have hs : typeF4RootPairing.root (root 0) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 16) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 16)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_21 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_22 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (22 : Fin 52) 1 = (1 : ℤ) • Pi.single (5 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 18) =
    (1 : ℤ) • v (root 1)
  have hs : typeF4RootPairing.root (root 1) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 18) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 18)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_23 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_24 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_25 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_26 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_27 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_28 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (28 : Fin 52) 1 = (1 : ℤ) • Pi.single (6 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 24) =
    (1 : ℤ) • v (root 2)
  have hs : typeF4RootPairing.root (root 2) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 24) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 24)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_29 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_30 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (30 : Fin 52) 1 = (1 : ℤ) • Pi.single (7 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 26) =
    (1 : ℤ) • v (root 3)
  have hs : typeF4RootPairing.root (root 3) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 26) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 26)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_31 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_32 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (32 : Fin 52) 1 = (1 : ℤ) • Pi.single (8 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 28) =
    (1 : ℤ) • v (root 4)
  have hs : typeF4RootPairing.root (root 4) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 28) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 28)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_33 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_34 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (34 : Fin 52) 1 = (1 : ℤ) • Pi.single (9 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 30) =
    (1 : ℤ) • v (root 5)
  have hs : typeF4RootPairing.root (root 5) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 30) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 30)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_35 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_36 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (36 : Fin 52) 1 = (1 : ℤ) • Pi.single (37 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 32) =
    (1 : ℤ) • v (root 33)
  have hs : typeF4RootPairing.root (root 33) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 32) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 32)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_37 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_38 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (38 : Fin 52) 1 = (1 : ℤ) • Pi.single (39 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 34) =
    (1 : ℤ) • v (root 35)
  have hs : typeF4RootPairing.root (root 35) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 34) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 34)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_39 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_40 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (40 : Fin 52) 1 = (1 : ℤ) • Pi.single (41 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 36) =
    (1 : ℤ) • v (root 37)
  have hs : typeF4RootPairing.root (root 37) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 36) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 36)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_41 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_42 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (42 : Fin 52) 1 = (1 : ℤ) • Pi.single (43 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 38) =
    (1 : ℤ) • v (root 39)
  have hs : typeF4RootPairing.root (root 39) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 38) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 38)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_43 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_44 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (44 : Fin 52) 1 = (1 : ℤ) • Pi.single (45 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 40) =
    (1 : ℤ) • v (root 41)
  have hs : typeF4RootPairing.root (root 41) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 40) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 40)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_45 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_46 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (46 : Fin 52) 1 = (1 : ℤ) • Pi.single (47 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 42) =
    (1 : ℤ) • v (root 43)
  have hs : typeF4RootPairing.root (root 43) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 42) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 42)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_47 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_48 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (48 : Fin 52) 1 = (1 : ℤ) • Pi.single (49 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 44) =
    (1 : ℤ) • v (root 45)
  have hs : typeF4RootPairing.root (root 45) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 44) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 44)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_49 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma middle2_column_50 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single (50 : Fin 52) 1 = (1 : ℤ) • Pi.single (51 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 2) *ᵥ v (root 46) =
    (1 : ℤ) • v (root 47)
  have hs : typeF4RootPairing.root (root 47) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (root 46) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 2) (root 46)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]) (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma middle2_column_51 :
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
  · apply not_root_of_norm <;> norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

/-- The actual middle simple-root operator, in the numbered lattice basis. -/
lemma reindex_middle2 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) = middleTable2 := by
  have hc (c : Fin 52) : reindex (eMatrix (typeF4RootPairing_baseEquiv 2)) *ᵥ
      Pi.single c 1 = middleTable2 *ᵥ Pi.single c 1 := by
    rw [middleTable2_column]
    fin_cases c
    · exact middle2_column_0
    · exact middle2_column_1
    · exact middle2_column_2
    · exact middle2_column_3
    · exact middle2_column_4
    · exact middle2_column_5
    · exact middle2_column_6
    · exact middle2_column_7
    · exact middle2_column_8
    · exact middle2_column_9
    · exact middle2_column_10
    · exact middle2_column_11
    · exact middle2_column_12
    · exact middle2_column_13
    · exact middle2_column_14
    · exact middle2_column_15
    · exact middle2_column_16
    · exact middle2_column_17
    · exact middle2_column_18
    · exact middle2_column_19
    · exact middle2_column_20
    · exact middle2_column_21
    · exact middle2_column_22
    · exact middle2_column_23
    · exact middle2_column_24
    · exact middle2_column_25
    · exact middle2_column_26
    · exact middle2_column_27
    · exact middle2_column_28
    · exact middle2_column_29
    · exact middle2_column_30
    · exact middle2_column_31
    · exact middle2_column_32
    · exact middle2_column_33
    · exact middle2_column_34
    · exact middle2_column_35
    · exact middle2_column_36
    · exact middle2_column_37
    · exact middle2_column_38
    · exact middle2_column_39
    · exact middle2_column_40
    · exact middle2_column_41
    · exact middle2_column_42
    · exact middle2_column_43
    · exact middle2_column_44
    · exact middle2_column_45
    · exact middle2_column_46
    · exact middle2_column_47
    · exact middle2_column_48
    · exact middle2_column_49
    · exact middle2_column_50
    · exact middle2_column_51
  ext i j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hc j) i

end
end ReeF4.SectionGeometry.LinearRadical.LeviDetection.RootCentralizer
