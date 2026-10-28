module

public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Coordinates
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.SparseCalculation
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4IntegralChevalleyRepresentation
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.RootStrings
public import Mathlib.LinearAlgebra.Matrix.Reindex
/-!
# Certification of the end-root Geck operator tables

Reindex the actual Cartan-plus-root lattice by the proved enumeration of F₄.
Each column of the positive end-root operators follows from Geck's Cartan,
negative-simple-root, root-sum, or zero-column formula. Squared Euclidean norms
certify the required root exclusions; the short-to-long strings have coefficient
two by the existing root-string theorem. The negative operators are obtained
by reversing the root coordinates.

The finite table computations use kernel reduction. No representation or
operator equality is assumed. Source: Geck's integral construction in
`IntegralGeckConstruction.lean`, GLS3 §1.12 and Table 2.4, type VI.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace ReeF4.Cartan.FieldSeparation.TraceValues
noncomputable section
open scoped Classical Matrix
set_option backward.isDefEq.respectTransparency false
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg

abbrev Basis := typeF4RootPairing_base.support ⊕ typeF4Roots

def basisEquiv : Fin 52 ≃ Basis :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr typeF4RootPairing_baseEquiv rootEquiv)

def reindex {S : Type*} [CommRing S] : Matrix Basis Basis S ≃+* Matrix (Fin 52) (Fin 52) S :=
  Matrix.reindexRingEquiv S basisEquiv.symm

lemma reindex_apply {S : Type*} [CommRing S] (A : Matrix Basis Basis S) (r c : Fin 52) :
    reindex A r c = A (basisEquiv r) (basisEquiv c) := rfl

lemma reindex_column (A : Matrix Basis Basis ℤ) (c k : Fin 52) (a : ℤ)
    (h : A *ᵥ Pi.single (basisEquiv c) 1 = a • Pi.single (basisEquiv k) 1) :
    reindex A *ᵥ Pi.single c 1 = a • Pi.single k 1 := by
  ext r
  have hh := congrFun h (basisEquiv r)
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, reindex_apply, Pi.smul_apply,
    Pi.single_apply, basisEquiv.injective.eq_iff] using hh

lemma reindex_column_zero (A : Matrix Basis Basis ℤ) (c : Fin 52)
    (h : A *ᵥ Pi.single (basisEquiv c) 1 = 0) :
    reindex A *ᵥ Pi.single c 1 = 0 := by
  ext r
  have hh := congrFun h (basisEquiv r)
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, reindex_apply, Pi.zero_apply] using hh

lemma not_root_of_norm (v : Vec 4) (h1 : dot v v ≠ 1) (h2 : dot v v ≠ 2) :
    v ∉ Set.range typeF4RootPairing.root := by
  rintro ⟨r, hr⟩
  change r.val = v at hr
  by_cases hl : IsLongRoot r
  · exact h2 (hr ▸ isLongRoot_norm r hl)
  · exact h1 (hr ▸ isShortRoot_norm r hl)

lemma bot_zero_of_norm (i : typeF4RootPairing_base.support) (j : typeF4Roots)
    (h1 : dot (j.val - i.val.val) (j.val - i.val.val) ≠ 1)
    (h2 : dot (j.val - i.val.val) (j.val - i.val.val) ≠ 2) :
    typeF4RootPairing.chainBotCoeff i j = 0 := by
  apply typeF4RootPairing.chainBotCoeff_eq_zero_iff.mpr
  exact Or.inr (not_root_of_norm _ h1 h2)

def flip : Basis → Basis
  | .inl i => .inl i
  | .inr j => .inr (-j)

lemma root_neg_value (r : typeF4Roots) :
    typeF4RootPairing.root (-r) = -typeF4RootPairing.root r := by
  rw [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
    typeF4RootPairing.reflection_apply_self]

lemma fMatrix_flip (i : typeF4RootPairing_base.support) (r c : Basis) :
    fMatrix i r c = eMatrix i (flip r) (flip c) := by
  rcases r with r | r <;> rcases c with c | c
  · rfl
  · change (if r = i ∧ c = i.val then (1 : ℤ) else 0) =
      if r = i ∧ -c = -i.val then 1 else 0
    simp only [neg_inj]
  · change (if r = -i.val then |typeF4RootPairing_base.cartanMatrix i c| else 0) =
      if -r = i.val then |typeF4RootPairing_base.cartanMatrix i c| else 0
    simp only [neg_eq_iff_eq_neg]
  · have hc : typeF4RootPairing.chainBotCoeff i (-c) =
        typeF4RootPairing.chainTopCoeff i c :=
      typeF4RootPairing.chainBotCoeff_reflectionPerm_right
    simp only [flip, fMatrix, eMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    simp only [root_neg_value, hc,
      ← sub_eq_add_neg, neg_eq_iff_eq_neg, neg_sub]
    split_ifs <;> rfl

set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

lemma root_simple_0 : root 22 = typeF4SimpleRootIndex 0 := by
  apply Subtype.ext
  ext q
  fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

lemma root_simple_3 : root 40 = typeF4SimpleRootIndex 3 := by
  apply Subtype.ext
  ext q
  fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

def columns0 (c : Fin 52) : Fin 52 × ℤ :=
  match c.val with
  | 25 => (0, 1)
  | 9 => (7, 1)
  | 6 => (8, 1)
  | 17 => (13, 1)
  | 19 => (15, 1)
  | 12 => (16, 1)
  | 14 => (18, 1)
  | 0 => (26, 2)
  | 1 => (26, 1)
  | 34 => (30, 1)
  | 35 => (31, 1)
  | 28 => (32, 1)
  | 29 => (33, 1)
  | 38 => (40, 1)
  | 39 => (41, 1)
  | 46 => (48, 1)
  | 47 => (49, 1)
  | _ => (0, 0)

lemma table_columns0 (c : Fin 52) :
    matrix positive0Linear *ᵥ Pi.single c 1 =
      (columns0 c).2 • Pi.single (columns0 c).1 1 := by
  simp only [Matrix.mulVec_single_one]
  revert c
  decide +kernel

private lemma eMatrix_0_column_0 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (0 : Fin 52) 1 = (2 : ℤ) • Pi.single (26 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    u (typeF4RootPairing_baseEquiv 0) = (2 : ℤ) • v (root 22)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_0]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma eMatrix_0_column_1 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (1 : Fin 52) 1 = (1 : ℤ) • Pi.single (26 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    u (typeF4RootPairing_baseEquiv 1) = (1 : ℤ) • v (root 22)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_0]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma eMatrix_0_column_2 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (2 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    u (typeF4RootPairing_baseEquiv 2) = 0
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma eMatrix_0_column_3 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (3 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    u (typeF4RootPairing_baseEquiv 3) = 0
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma eMatrix_0_column_4 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (4 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 0) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_5 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (5 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 1) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_6 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (6 : Fin 52) 1 = (1 : ℤ) • Pi.single (8 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 2) = (1 : ℤ) • v (root 4)
  have hs : typeF4RootPairing.root (root 4) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 2) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 2)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_7 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (7 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 3) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_8 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (8 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 4) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_9 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (9 : Fin 52) 1 = (1 : ℤ) • Pi.single (7 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 5) = (1 : ℤ) • v (root 3)
  have hs : typeF4RootPairing.root (root 3) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 5) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 5)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_10 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (10 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 6) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_11 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (11 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 7) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_12 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (12 : Fin 52) 1 = (1 : ℤ) • Pi.single (16 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 8) = (1 : ℤ) • v (root 12)
  have hs : typeF4RootPairing.root (root 12) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 8) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 8)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_13 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (13 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 9) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_14 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (14 : Fin 52) 1 = (1 : ℤ) • Pi.single (18 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 10) = (1 : ℤ) • v (root 14)
  have hs : typeF4RootPairing.root (root 14) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 10) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 10)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_15 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (15 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 11) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_16 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (16 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 12) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_17 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (17 : Fin 52) 1 = (1 : ℤ) • Pi.single (13 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 13) = (1 : ℤ) • v (root 9)
  have hs : typeF4RootPairing.root (root 9) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 13) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 13)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_18 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (18 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 14) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_19 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (19 : Fin 52) 1 = (1 : ℤ) • Pi.single (15 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 15) = (1 : ℤ) • v (root 11)
  have hs : typeF4RootPairing.root (root 11) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 15) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 15)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_20 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (20 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 16) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_21 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (21 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 17) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_22 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (22 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 18) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_23 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (23 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 19) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_24 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (24 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 20) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 2) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_25 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (25 : Fin 52) 1 = (1 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 21) = (1 : ℤ) • u (typeF4RootPairing_baseEquiv 0)
  have hn : root 21 = -(typeF4RootPairing_baseEquiv 0).val := by
    apply typeF4RootPairing.root.injective
    rw [root_neg_value]
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [hn, eMatrix_mulVec_v_neg, one_smul]

private lemma eMatrix_0_column_26 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (26 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 22) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_27 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (27 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 23) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_28 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (28 : Fin 52) 1 = (1 : ℤ) • Pi.single (32 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 24) = (1 : ℤ) • v (root 28)
  have hs : typeF4RootPairing.root (root 28) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 24) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 24)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_29 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (29 : Fin 52) 1 = (1 : ℤ) • Pi.single (33 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 25) = (1 : ℤ) • v (root 29)
  have hs : typeF4RootPairing.root (root 29) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 25) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 25)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_30 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (30 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 26) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_31 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (31 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 27) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_32 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (32 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 28) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_33 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (33 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 29) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_34 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (34 : Fin 52) 1 = (1 : ℤ) • Pi.single (30 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 30) = (1 : ℤ) • v (root 26)
  have hs : typeF4RootPairing.root (root 26) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 30) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 30)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_35 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (35 : Fin 52) 1 = (1 : ℤ) • Pi.single (31 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 31) = (1 : ℤ) • v (root 27)
  have hs : typeF4RootPairing.root (root 27) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 31) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 31)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_36 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (36 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 32) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_37 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (37 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 33) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_38 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (38 : Fin 52) 1 = (1 : ℤ) • Pi.single (40 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 34) = (1 : ℤ) • v (root 36)
  have hs : typeF4RootPairing.root (root 36) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 34) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 34)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_39 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (39 : Fin 52) 1 = (1 : ℤ) • Pi.single (41 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 35) = (1 : ℤ) • v (root 37)
  have hs : typeF4RootPairing.root (root 37) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 35) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 35)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_40 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (40 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 36) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_41 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (41 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 37) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_42 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (42 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 38) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_43 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (43 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 39) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_44 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (44 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 40) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_45 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (45 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 41) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_46 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (46 : Fin 52) 1 = (1 : ℤ) • Pi.single (48 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 42) = (1 : ℤ) • v (root 44)
  have hs : typeF4RootPairing.root (root 44) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 42) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 42)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_47 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (47 : Fin 52) 1 = (1 : ℤ) • Pi.single (49 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ
    v (root 43) = (1 : ℤ) • v (root 45)
  have hs : typeF4RootPairing.root (root 45) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 0) +
      typeF4RootPairing.root (root 43) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 0) (root 43)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_0_column_48 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (48 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 44) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_49 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (49 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 45) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_50 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (50 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 46) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_0_column_51 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) *ᵥ
      Pi.single (51 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 0) *ᵥ v (root 47) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

lemma eMatrix_0 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 0)) = matrix positive0Linear := by
  apply Matrix.ext_col
  intro c
  rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_single_one, table_columns0]
  fin_cases c
  · exact eMatrix_0_column_0
  · exact eMatrix_0_column_1
  · exact eMatrix_0_column_2
  · exact eMatrix_0_column_3
  · exact eMatrix_0_column_4
  · exact eMatrix_0_column_5
  · exact eMatrix_0_column_6
  · exact eMatrix_0_column_7
  · exact eMatrix_0_column_8
  · exact eMatrix_0_column_9
  · exact eMatrix_0_column_10
  · exact eMatrix_0_column_11
  · exact eMatrix_0_column_12
  · exact eMatrix_0_column_13
  · exact eMatrix_0_column_14
  · exact eMatrix_0_column_15
  · exact eMatrix_0_column_16
  · exact eMatrix_0_column_17
  · exact eMatrix_0_column_18
  · exact eMatrix_0_column_19
  · exact eMatrix_0_column_20
  · exact eMatrix_0_column_21
  · exact eMatrix_0_column_22
  · exact eMatrix_0_column_23
  · exact eMatrix_0_column_24
  · exact eMatrix_0_column_25
  · exact eMatrix_0_column_26
  · exact eMatrix_0_column_27
  · exact eMatrix_0_column_28
  · exact eMatrix_0_column_29
  · exact eMatrix_0_column_30
  · exact eMatrix_0_column_31
  · exact eMatrix_0_column_32
  · exact eMatrix_0_column_33
  · exact eMatrix_0_column_34
  · exact eMatrix_0_column_35
  · exact eMatrix_0_column_36
  · exact eMatrix_0_column_37
  · exact eMatrix_0_column_38
  · exact eMatrix_0_column_39
  · exact eMatrix_0_column_40
  · exact eMatrix_0_column_41
  · exact eMatrix_0_column_42
  · exact eMatrix_0_column_43
  · exact eMatrix_0_column_44
  · exact eMatrix_0_column_45
  · exact eMatrix_0_column_46
  · exact eMatrix_0_column_47
  · exact eMatrix_0_column_48
  · exact eMatrix_0_column_49
  · exact eMatrix_0_column_50
  · exact eMatrix_0_column_51

def columns3 (c : Fin 52) : Fin 52 × ℤ :=
  match c.val with
  | 43 => (3, 1)
  | 51 => (5, 1)
  | 39 => (6, 1)
  | 41 => (8, 1)
  | 42 => (10, 1)
  | 47 => (14, 2)
  | 49 => (18, 2)
  | 50 => (22, 2)
  | 37 => (24, 2)
  | 38 => (28, 2)
  | 40 => (32, 2)
  | 4 => (36, 1)
  | 21 => (37, 1)
  | 17 => (38, 1)
  | 13 => (40, 1)
  | 2 => (44, 1)
  | 3 => (44, 2)
  | 11 => (45, 1)
  | 9 => (46, 1)
  | 35 => (47, 1)
  | 7 => (48, 1)
  | 31 => (49, 1)
  | 27 => (50, 1)
  | _ => (0, 0)

lemma table_columns3 (c : Fin 52) :
    matrix positive3Linear *ᵥ Pi.single c 1 =
      (columns3 c).2 • Pi.single (columns3 c).1 1 := by
  simp only [Matrix.mulVec_single_one]
  revert c
  decide +kernel

private lemma eMatrix_3_column_0 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (0 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    u (typeF4RootPairing_baseEquiv 0) = 0
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma eMatrix_3_column_1 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (1 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    u (typeF4RootPairing_baseEquiv 1) = 0
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma eMatrix_3_column_2 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (2 : Fin 52) 1 = (1 : ℤ) • Pi.single (44 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    u (typeF4RootPairing_baseEquiv 2) = (1 : ℤ) • v (root 40)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_3]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma eMatrix_3_column_3 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (3 : Fin 52) 1 = (2 : ℤ) • Pi.single (44 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    u (typeF4RootPairing_baseEquiv 3) = (2 : ℤ) • v (root 40)
  rw [eMatrix_mulVec_u, typeF4RootPairing_base_cartan_apply,
    typeF4RootPairing_baseEquiv_val, ← root_simple_3]
  norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma eMatrix_3_column_4 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (4 : Fin 52) 1 = (1 : ℤ) • Pi.single (36 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 0) = (1 : ℤ) • v (root 32)
  have hs : typeF4RootPairing.root (root 32) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 0) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 0)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_5 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (5 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 1) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_6 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (6 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 2) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_7 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (7 : Fin 52) 1 = (1 : ℤ) • Pi.single (48 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 3) = (1 : ℤ) • v (root 44)
  have hs : typeF4RootPairing.root (root 44) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 3) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 3)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_8 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (8 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 4) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_9 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (9 : Fin 52) 1 = (1 : ℤ) • Pi.single (46 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 5) = (1 : ℤ) • v (root 42)
  have hs : typeF4RootPairing.root (root 42) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 5) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 5)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_10 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (10 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 6) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_11 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (11 : Fin 52) 1 = (1 : ℤ) • Pi.single (45 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 7) = (1 : ℤ) • v (root 41)
  have hs : typeF4RootPairing.root (root 41) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 7) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 7)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_12 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (12 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 8) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_13 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (13 : Fin 52) 1 = (1 : ℤ) • Pi.single (40 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 9) = (1 : ℤ) • v (root 36)
  have hs : typeF4RootPairing.root (root 36) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 9) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 9)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_14 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (14 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 10) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_15 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (15 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 11) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_16 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (16 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 12) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_17 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (17 : Fin 52) 1 = (1 : ℤ) • Pi.single (38 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 13) = (1 : ℤ) • v (root 34)
  have hs : typeF4RootPairing.root (root 34) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 13) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 13)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_18 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (18 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 14) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_19 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (19 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 15) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_20 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (20 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 16) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_21 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (21 : Fin 52) 1 = (1 : ℤ) • Pi.single (37 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 17) = (1 : ℤ) • v (root 33)
  have hs : typeF4RootPairing.root (root 33) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 17) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 17)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_22 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (22 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 18) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_23 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (23 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 19) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_24 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (24 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 20) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_25 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (25 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 21) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_26 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (26 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 22) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_27 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (27 : Fin 52) 1 = (1 : ℤ) • Pi.single (50 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 23) = (1 : ℤ) • v (root 46)
  have hs : typeF4RootPairing.root (root 46) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 23) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 23)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_28 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (28 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 24) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_29 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (29 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 25) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_30 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (30 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 26) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_31 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (31 : Fin 52) 1 = (1 : ℤ) • Pi.single (49 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 27) = (1 : ℤ) • v (root 45)
  have hs : typeF4RootPairing.root (root 45) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 27) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 27)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_32 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (32 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 28) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_33 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (33 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 29) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_34 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (34 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 30) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_35 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (35 : Fin 52) 1 = (1 : ℤ) • Pi.single (47 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 31) = (1 : ℤ) • v (root 43)
  have hs : typeF4RootPairing.root (root 43) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 31) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 31)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_36 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (36 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 32) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 1) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_37 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (37 : Fin 52) 1 = (2 : ℤ) • Pi.single (24 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 33) = (2 : ℤ) • v (root 20)
  have hs : typeF4RootPairing.root (root 20) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 33) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 3).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 3)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 20) := by
    by_contra hn
    have hh := isShortRoot_norm (root 20) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num

private lemma eMatrix_3_column_38 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (38 : Fin 52) 1 = (2 : ℤ) • Pi.single (28 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 34) = (2 : ℤ) • v (root 24)
  have hs : typeF4RootPairing.root (root 24) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 34) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 3).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 3)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 24) := by
    by_contra hn
    have hh := isShortRoot_norm (root 24) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num

private lemma eMatrix_3_column_39 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (39 : Fin 52) 1 = (1 : ℤ) • Pi.single (6 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 35) = (1 : ℤ) • v (root 2)
  have hs : typeF4RootPairing.root (root 2) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 35) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 35)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_40 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (40 : Fin 52) 1 = (2 : ℤ) • Pi.single (32 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 36) = (2 : ℤ) • v (root 28)
  have hs : typeF4RootPairing.root (root 28) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 36) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 3).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 3)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 28) := by
    by_contra hn
    have hh := isShortRoot_norm (root 28) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num

private lemma eMatrix_3_column_41 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (41 : Fin 52) 1 = (1 : ℤ) • Pi.single (8 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 37) = (1 : ℤ) • v (root 4)
  have hs : typeF4RootPairing.root (root 4) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 37) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 37)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_42 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (42 : Fin 52) 1 = (1 : ℤ) • Pi.single (10 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 38) = (1 : ℤ) • v (root 6)
  have hs : typeF4RootPairing.root (root 6) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 38) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 38)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

private lemma eMatrix_3_column_43 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (43 : Fin 52) 1 = (1 : ℤ) • Pi.single (3 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 39) = (1 : ℤ) • u (typeF4RootPairing_baseEquiv 3)
  have hn : root 39 = -(typeF4RootPairing_baseEquiv 3).val := by
    apply typeF4RootPairing.root.injective
    rw [root_neg_value]
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [hn, eMatrix_mulVec_v_neg, one_smul]

private lemma eMatrix_3_column_44 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (44 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 40) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_45 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (45 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 41) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_46 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (46 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 42) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_47 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (47 : Fin 52) 1 = (2 : ℤ) • Pi.single (14 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 43) = (2 : ℤ) • v (root 10)
  have hs : typeF4RootPairing.root (root 10) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 43) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 3).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 3)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 10) := by
    by_contra hn
    have hh := isShortRoot_norm (root 10) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num

private lemma eMatrix_3_column_48 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (48 : Fin 52) 1 = (0 : ℤ) • Pi.single (0 : Fin 52) 1 := by
  rw [zero_smul]
  apply reindex_column_zero
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ v (root 44) = 0
  apply eMatrix_mulVec_v_zero
  · intro h
    have hh := congrArg (fun r => typeF4RootPairing.root r 0) h
    simp only [root_neg_value] at hh
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  · apply not_root_of_norm
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    · norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma eMatrix_3_column_49 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (49 : Fin 52) 1 = (2 : ℤ) • Pi.single (18 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 45) = (2 : ℤ) • v (root 14)
  have hs : typeF4RootPairing.root (root 14) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 45) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 3).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 3)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 14) := by
    by_contra hn
    have hh := isShortRoot_norm (root 14) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num

private lemma eMatrix_3_column_50 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (50 : Fin 52) 1 = (2 : ℤ) • Pi.single (22 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 46) = (2 : ℤ) • v (root 18)
  have hs : typeF4RootPairing.root (root 18) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 46) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hi : IsShortRoot (typeF4RootPairing_baseEquiv 3).val := by
    change ¬ IsLongRoot (typeF4SimpleRootIndex 3)
    rw [IsLongRoot, typeF4SimpleRootIndex_mem_pair_iff]
    decide
  have hk : IsLongRoot (root 18) := by
    by_contra hn
    have hh := isShortRoot_norm (root 18) hn
    norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord] at hh
  rw [WordRelations.chainBotCoeff_short_add_long hi hk hs]
  norm_num

private lemma eMatrix_3_column_51 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) *ᵥ
      Pi.single (51 : Fin 52) 1 = (1 : ℤ) • Pi.single (5 : Fin 52) 1 := by
  apply reindex_column
  change eMatrix (typeF4RootPairing_baseEquiv 3) *ᵥ
    v (root 47) = (1 : ℤ) • v (root 1)
  have hs : typeF4RootPairing.root (root 1) =
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (root 47) := by
    ext q
    fin_cases q <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  rw [eMatrix_mulVec_v_add hs]
  have hb := bot_zero_of_norm (typeF4RootPairing_baseEquiv 3) (root 47)
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
    (by norm_num [dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord])
  rw [hb]
  norm_num

lemma eMatrix_3 :
    reindex (eMatrix (typeF4RootPairing_baseEquiv 3)) = matrix positive3Linear := by
  apply Matrix.ext_col
  intro c
  rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_single_one, table_columns3]
  fin_cases c
  · exact eMatrix_3_column_0
  · exact eMatrix_3_column_1
  · exact eMatrix_3_column_2
  · exact eMatrix_3_column_3
  · exact eMatrix_3_column_4
  · exact eMatrix_3_column_5
  · exact eMatrix_3_column_6
  · exact eMatrix_3_column_7
  · exact eMatrix_3_column_8
  · exact eMatrix_3_column_9
  · exact eMatrix_3_column_10
  · exact eMatrix_3_column_11
  · exact eMatrix_3_column_12
  · exact eMatrix_3_column_13
  · exact eMatrix_3_column_14
  · exact eMatrix_3_column_15
  · exact eMatrix_3_column_16
  · exact eMatrix_3_column_17
  · exact eMatrix_3_column_18
  · exact eMatrix_3_column_19
  · exact eMatrix_3_column_20
  · exact eMatrix_3_column_21
  · exact eMatrix_3_column_22
  · exact eMatrix_3_column_23
  · exact eMatrix_3_column_24
  · exact eMatrix_3_column_25
  · exact eMatrix_3_column_26
  · exact eMatrix_3_column_27
  · exact eMatrix_3_column_28
  · exact eMatrix_3_column_29
  · exact eMatrix_3_column_30
  · exact eMatrix_3_column_31
  · exact eMatrix_3_column_32
  · exact eMatrix_3_column_33
  · exact eMatrix_3_column_34
  · exact eMatrix_3_column_35
  · exact eMatrix_3_column_36
  · exact eMatrix_3_column_37
  · exact eMatrix_3_column_38
  · exact eMatrix_3_column_39
  · exact eMatrix_3_column_40
  · exact eMatrix_3_column_41
  · exact eMatrix_3_column_42
  · exact eMatrix_3_column_43
  · exact eMatrix_3_column_44
  · exact eMatrix_3_column_45
  · exact eMatrix_3_column_46
  · exact eMatrix_3_column_47
  · exact eMatrix_3_column_48
  · exact eMatrix_3_column_49
  · exact eMatrix_3_column_50
  · exact eMatrix_3_column_51

end
end ReeF4.Cartan.FieldSeparation.TraceValues
