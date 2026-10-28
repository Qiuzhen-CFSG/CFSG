module

public import Theory.AlgebraicGroup.RootSystems.SymplecticRootSubgroups
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteGeneration

/-!
# Elementary generation of the standard symplectic group

The explicit standard type-C root subgroups generate every point of the
standard symplectic carrier, over an arbitrary algebraically closed field and
in every rank, including rank zero.  The proof is direct symplectic matrix
elimination.  Symmetric upper and lower unipotent blocks are products of the
short and long root matrices, while general-linear diagonal blocks are built
from mixed roots and the characteristic-free six-factor rank-one diagonal
identity.  Gaussian transvection generation then handles every invertible
linear block.

For a general symplectic matrix, a symmetric row operation makes its
upper-left block invertible.  The resulting matrix admits the block
factorization
`[1,0; C A⁻¹,1] [A,0;0,A⁻ᵀ] [1,A⁻¹ B;0,1]`.
All three factors are elementary by the preceding calculations, and the row
operation can be cancelled by another elementary factor.  This argument uses
only the defining symplectic block equations and works in every
characteristic.  Its two linear-algebra inputs are Mathlib's transvection
induction for an invertible matrix and the constructive pivot argument behind
the symmetric rank-normal-form lemma; the latter is reproduced here because
the library result exposing it is private.

Finally, the finite connected closed-subgroup generation theorem makes the
root-generated abstract subgroup closed.  Each one-parameter root subgroup
lies in its identity component, so the generation equality forces the whole
standard carrier to be connected.  The construction is the classical
symplectic row/column elimination for the standard type-C matrix model; no
classification or general Chevalley-group construction is used.
-/

open scoped BigOperators

universe u

set_option linter.style.haveILetI false

open Matrix

namespace Theory.AlgebraicGroup

open StandardRootSystem

variable {k : Type u} [Field k] [IsAlgClosed k]

private abbrev SymplecticPoint (m : ℕ) :=
  Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety

private abbrev SymplecticMatrix (m : ℕ) :=
  Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k

private noncomputable def symplecticRootGenerated (m : ℕ) :
    Subgroup (SymplecticPoint (k := k) m) :=
  Subgroup.closure (⋃ r : TypeCRootIndex m,
    (symplecticRootSubgroup (k := k) m r : Set (SymplecticPoint (k := k) m)))

private def IsElementaryMatrix (m : ℕ) (M : SymplecticMatrix (k := k) m) : Prop :=
  ∃ x : SymplecticPoint (k := k) m,
    x ∈ symplecticRootGenerated (k := k) m ∧ symplecticClosedPointMatrix m x = M

private lemma symplecticClosedPointMatrix_mem (m : ℕ)
    (x : SymplecticPoint (k := k) m) :
    symplecticClosedPointMatrix m x ∈ Matrix.symplecticGroup (Fin m) k := by
  change symplecticMatrix m (standardSymplecticClosedSubgroupPoints m x).1 ∈
    Matrix.symplecticGroup (Fin m) k
  exact (mem_bilinearIsometrySubgroup_iff_symplecticMatrix m _).mp
    (standardSymplecticClosedSubgroupPoints m x).property

private lemma isElementaryMatrix_one (m : ℕ) :
    IsElementaryMatrix (k := k) m 1 := by
  refine ⟨1, (symplecticRootGenerated (k := k) m).one_mem, ?_⟩
  let A := symplecticClosedPointMatrix (k := k) m 1
  have hAunit : IsUnit A := A.isUnit_iff_isUnit_det.mpr
    (SymplecticGroup.symplectic_det (symplecticClosedPointMatrix_mem m 1))
  apply hAunit.mul_left_cancel
  simpa [A] using (symplecticClosedPointMatrix_mul (k := k) m 1 1).symm

private lemma IsElementaryMatrix.mul {m : ℕ} {A B : SymplecticMatrix (k := k) m}
    (hA : IsElementaryMatrix (k := k) m A)
    (hB : IsElementaryMatrix (k := k) m B) :
    IsElementaryMatrix (k := k) m (A * B) := by
  rcases hA with ⟨a, ha, rfl⟩
  rcases hB with ⟨b, hb, rfl⟩
  exact ⟨a * b, (symplecticRootGenerated (k := k) m).mul_mem ha hb,
    symplecticClosedPointMatrix_mul m a b⟩

private lemma isElementaryMatrix_root (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    IsElementaryMatrix (k := k) m (symplecticRootMatrix m r a) := by
  refine ⟨symplecticRootPoint m r a, ?_, symplecticClosedPointMatrix_rootPoint m r a⟩
  apply Subgroup.subset_closure
  apply Set.mem_iUnion_of_mem r
  change symplecticRootPoint m r a ∈ (symplecticRootMorphism m r).image
  exact ⟨kPlusPoint a, symplecticRootMorphism_kPlusPoint m r a⟩

private def positiveRootSign : ({-1, 1} : Set ℝ) := ⟨1, by simp⟩
private def negativeRootSign : ({-1, 1} : Set ℝ) := ⟨-1, by simp⟩

private def upperUnipotent (m : ℕ) (X : Matrix (Fin m) (Fin m) k) :
    SymplecticMatrix (k := k) m := Matrix.fromBlocks 1 X 0 1

private def lowerUnipotent (m : ℕ) (X : Matrix (Fin m) (Fin m) k) :
    SymplecticMatrix (k := k) m := Matrix.fromBlocks 1 0 X 1

omit [IsAlgClosed k] in
private lemma upperUnipotent_zero (m : ℕ) :
    upperUnipotent (k := k) m 0 = 1 := by
  simp [upperUnipotent, Matrix.fromBlocks_one]

omit [IsAlgClosed k] in
private lemma lowerUnipotent_zero (m : ℕ) :
    lowerUnipotent (k := k) m 0 = 1 := by
  simp [lowerUnipotent, Matrix.fromBlocks_one]

omit [IsAlgClosed k] in
private lemma upperUnipotent_add (m : ℕ) (X Y : Matrix (Fin m) (Fin m) k) :
    upperUnipotent m (X + Y) = upperUnipotent m X * upperUnipotent m Y := by
  simp [upperUnipotent, Matrix.fromBlocks_multiply]
  abel

omit [IsAlgClosed k] in
private lemma lowerUnipotent_add (m : ℕ) (X Y : Matrix (Fin m) (Fin m) k) :
    lowerUnipotent m (X + Y) = lowerUnipotent m X * lowerUnipotent m Y := by
  simp [lowerUnipotent, Matrix.fromBlocks_multiply]

private lemma isElementaryMatrix_upper_diagonal
    (m : ℕ) (i : Fin m) (a : k) :
    IsElementaryMatrix (k := k) m
      (upperUnipotent m (Matrix.single i i a)) := by
  simpa [upperUnipotent, symplecticRootMatrix] using
    isElementaryMatrix_root (k := k) m (.inr ⟨i, false⟩) a

private lemma isElementaryMatrix_lower_diagonal
    (m : ℕ) (i : Fin m) (a : k) :
    IsElementaryMatrix (k := k) m
      (lowerUnipotent m (Matrix.single i i a)) := by
  simpa [lowerUnipotent, symplecticRootMatrix] using
    isElementaryMatrix_root (k := k) m (.inr ⟨i, true⟩) a

private lemma isElementaryMatrix_upper_pair
    (m : ℕ) (i j : Fin m) (hij : i < j) (a : k) :
    IsElementaryMatrix (k := k) m
      (upperUnipotent m (Matrix.single i j a + Matrix.single j i a)) := by
  let r : TypeCRootIndex m := .inl
    ⟨⟨⟨i, j⟩, hij⟩, positiveRootSign, positiveRootSign⟩
  simpa [r, upperUnipotent, symplecticRootMatrix, positiveRootSign] using
    isElementaryMatrix_root (k := k) m r a

private lemma isElementaryMatrix_lower_pair
    (m : ℕ) (i j : Fin m) (hij : i < j) (a : k) :
    IsElementaryMatrix (k := k) m
      (lowerUnipotent m (Matrix.single i j a + Matrix.single j i a)) := by
  let r : TypeCRootIndex m := .inl
    ⟨⟨⟨i, j⟩, hij⟩, negativeRootSign, negativeRootSign⟩
  have hroot := isElementaryMatrix_root (k := k) m r a
  norm_num [r, lowerUnipotent, symplecticRootMatrix, negativeRootSign] at hroot
  exact hroot

private def symmetricEntry (m : ℕ) (X : Matrix (Fin m) (Fin m) k)
    (p : Fin m × Fin m) : Matrix (Fin m) (Fin m) k :=
  if _h : p.1 = p.2 then Matrix.single p.1 p.1 (X p.1 p.1)
  else if p.1 < p.2 then
    Matrix.single p.1 p.2 (X p.1 p.2) + Matrix.single p.2 p.1 (X p.1 p.2)
  else 0

omit [IsAlgClosed k] in
private lemma matrix_fintype_sum_apply {m : ℕ}
    (f : Fin m × Fin m → Matrix (Fin m) (Fin m) k) (i j : Fin m) :
    (∑ p, f p) i j = ∑ p, f p i j := by
  simpa using Matrix.sum_apply i j Finset.univ f

omit [IsAlgClosed k] in
private lemma symmetric_eq_sum_entries (m : ℕ) (X : Matrix (Fin m) (Fin m) k)
    (hX : X.IsSymm) :
    X = ∑ p : Fin m × Fin m, symmetricEntry m X p := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    rw [matrix_fintype_sum_apply]
    rw [Finset.sum_eq_single (i, i)]
    · simp [symmetricEntry]
    · rintro ⟨a, b⟩ _ hab
      simp only [symmetricEntry]
      split_ifs with hab' hlt <;> simp [Matrix.single_apply]
      all_goals grind
    · simp
  · rcases lt_or_gt_of_ne hij with hij | hji
    · rw [matrix_fintype_sum_apply]
      rw [Finset.sum_eq_single (i, j)]
      · simp [symmetricEntry, hij, hij.ne]
      · rintro ⟨a, b⟩ _ hab
        simp only [symmetricEntry]
        split_ifs with hab' hlt <;> simp [Matrix.single_apply]
        all_goals grind
      · simp
    · have hji' : j < i := hji
      have hsymm : X j i = X i j := by
        simpa [Matrix.IsSymm] using congrFun (congrFun hX.eq i) j
      rw [matrix_fintype_sum_apply]
      rw [Finset.sum_eq_single (j, i)]
      · simp [symmetricEntry, hji', hji'.ne, hsymm]
      · rintro ⟨a, b⟩ _ hab
        simp only [symmetricEntry]
        split_ifs with hab' hlt <;> simp [Matrix.single_apply]
        all_goals grind
      · simp

private lemma isElementaryMatrix_upper_sum_entries
    (m : ℕ) (X : Matrix (Fin m) (Fin m) k) :
    IsElementaryMatrix (k := k) m
      (upperUnipotent m (∑ p : Fin m × Fin m, symmetricEntry m X p)) := by
  classical
  refine Finset.sum_induction (s := Finset.univ) (f := symmetricEntry m X)
    (p := fun Y => IsElementaryMatrix (k := k) m (upperUnipotent m Y)) ?_ ?_ ?_
  · intro A B hA hB
    rw [upperUnipotent_add]
    exact hA.mul hB
  · simpa [upperUnipotent_zero] using isElementaryMatrix_one (k := k) m
  · intro p hp
    simp only [symmetricEntry]
    split_ifs with hdiag hlt
    · exact isElementaryMatrix_upper_diagonal (k := k) m p.1 (X p.1 p.1)
    · exact isElementaryMatrix_upper_pair (k := k) m p.1 p.2 hlt (X p.1 p.2)
    · simpa [upperUnipotent_zero] using isElementaryMatrix_one (k := k) m

private lemma isElementaryMatrix_lower_sum_entries
    (m : ℕ) (X : Matrix (Fin m) (Fin m) k) :
    IsElementaryMatrix (k := k) m
      (lowerUnipotent m (∑ p : Fin m × Fin m, symmetricEntry m X p)) := by
  classical
  refine Finset.sum_induction (s := Finset.univ) (f := symmetricEntry m X)
    (p := fun Y => IsElementaryMatrix (k := k) m (lowerUnipotent m Y)) ?_ ?_ ?_
  · intro A B hA hB
    rw [lowerUnipotent_add]
    exact hA.mul hB
  · simpa [lowerUnipotent_zero] using isElementaryMatrix_one (k := k) m
  · intro p hp
    simp only [symmetricEntry]
    split_ifs with hdiag hlt
    · exact isElementaryMatrix_lower_diagonal (k := k) m p.1 (X p.1 p.1)
    · exact isElementaryMatrix_lower_pair (k := k) m p.1 p.2 hlt (X p.1 p.2)
    · simpa [lowerUnipotent_zero] using isElementaryMatrix_one (k := k) m

private lemma isElementaryMatrix_upper (m : ℕ) (X : Matrix (Fin m) (Fin m) k)
    (hX : X.IsSymm) :
    IsElementaryMatrix (k := k) m (upperUnipotent m X) := by
  rw [symmetric_eq_sum_entries m X hX]
  exact isElementaryMatrix_upper_sum_entries (k := k) m X

private lemma isElementaryMatrix_lower (m : ℕ) (X : Matrix (Fin m) (Fin m) k)
    (hX : X.IsSymm) :
    IsElementaryMatrix (k := k) m (lowerUnipotent m X) := by
  rw [symmetric_eq_sum_entries m X hX]
  exact isElementaryMatrix_lower_sum_entries (k := k) m X

private noncomputable def linearBlock (m : ℕ) (A : Matrix (Fin m) (Fin m) k) :
    SymplecticMatrix (k := k) m :=
  Matrix.fromBlocks A 0 0 A⁻¹.transpose

omit [IsAlgClosed k] in
private lemma linearBlock_one (m : ℕ) : linearBlock (k := k) m 1 = 1 := by
  simp [linearBlock, Matrix.fromBlocks_one]

omit [IsAlgClosed k] in
private lemma linearBlock_mul (m : ℕ) (A B : Matrix (Fin m) (Fin m) k) :
    linearBlock m (A * B) = linearBlock m A * linearBlock m B := by
  simp [linearBlock, Matrix.fromBlocks_multiply, Matrix.mul_inv_rev,
    Matrix.transpose_mul]

omit [IsAlgClosed k] in
private lemma ringInverse_mulSingle
    (m : ℕ) (i : Fin m) (a : k) (ha : a ≠ 0) :
    Ring.inverse (Pi.mulSingle i a : Fin m → k) = Pi.mulSingle i a⁻¹ := by
  classical
  let f : Fin m → k := Pi.mulSingle i a
  let g : Fin m → k := Pi.mulSingle i a⁻¹
  have hfg : f * g = 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [f, g, ha]
    · simp [f, g, hji]
  have hgf : g * f = 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [f, g, ha]
    · simp [f, g, hji]
  have hf : IsUnit f := ⟨⟨f, g, hfg, hgf⟩, rfl⟩
  exact left_inv_eq_right_inv (Ring.inverse_mul_cancel f hf) hfg

omit [IsAlgClosed k] in
private lemma coordinateLinearBlock_factorization
    (m : ℕ) (i : Fin m) (a : k) (ha : a ≠ 0) :
    linearBlock m (Matrix.diagonal (Pi.mulSingle i a)) =
      upperUnipotent m (Matrix.single i i a) *
        lowerUnipotent m (Matrix.single i i (-a⁻¹)) *
        upperUnipotent m (Matrix.single i i a) *
        upperUnipotent m (Matrix.single i i (-1)) *
        lowerUnipotent m (Matrix.single i i 1) *
        upperUnipotent m (Matrix.single i i (-1)) := by
  classical
  rw [linearBlock, Matrix.inv_diagonal, ringInverse_mulSingle m i a ha]
  ext (p | p) (q | q) <;>
    simp [upperUnipotent, lowerUnipotent, Matrix.fromBlocks_multiply,
      Matrix.single_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Pi.mulSingle_apply, add_mul, ha]
  all_goals
    by_cases hpq : p = q
    · subst q
      by_cases hpi : p = i
      · subst p
        simp
      · have hip : i ≠ p := Ne.symm hpi
        simp [hpi, hip]
    · have hpair : ¬(i = p ∧ i = q) := by grind
      simp [hpq, hpair]

private lemma isElementaryMatrix_coordinateLinearBlock
    (m : ℕ) (i : Fin m) (a : k) (ha : a ≠ 0) :
    IsElementaryMatrix (k := k) m
      (linearBlock m (Matrix.diagonal (Pi.mulSingle i a))) := by
  rw [coordinateLinearBlock_factorization m i a ha]
  exact (((((isElementaryMatrix_upper_diagonal (k := k) m i a).mul
      (isElementaryMatrix_lower_diagonal (k := k) m i (-a⁻¹))).mul
      (isElementaryMatrix_upper_diagonal (k := k) m i a)).mul
      (isElementaryMatrix_upper_diagonal (k := k) m i (-1))).mul
      (isElementaryMatrix_lower_diagonal (k := k) m i 1)).mul
      (isElementaryMatrix_upper_diagonal (k := k) m i (-1))

private lemma isElementaryMatrix_linearBlock_diagonal
    (m : ℕ) (D : Fin m → k) (hD : (Matrix.diagonal D).det ≠ 0) :
    IsElementaryMatrix (k := k) m (linearBlock m (Matrix.diagonal D)) := by
  classical
  have hDne (i : Fin m) : D i ≠ 0 := by
    intro hi
    apply hD
    rw [Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let d : Fin m → kˣ := fun i => Units.mk0 (D i) (hDne i)
  change IsElementaryMatrix (k := k) m
    (linearBlock m (Matrix.diagonal fun i => (d i : k)))
  refine Pi.mulSingle_induction
    (p := fun z : Fin m → kˣ => IsElementaryMatrix (k := k) m
      (linearBlock m (Matrix.diagonal fun i => (z i : k)))) d ?_ ?_ ?_
  · simpa [linearBlock_one] using isElementaryMatrix_one (k := k) m
  · intro f g hf hg
    rw [show Matrix.diagonal (fun i => ((f * g) i : k)) =
        Matrix.diagonal (fun i => (f i : k)) * Matrix.diagonal (fun i => (g i : k)) by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]]
    rw [linearBlock_mul]
    exact hf.mul hg
  · intro i a
    have hcoe :
        (fun j : Fin m => (((Pi.mulSingle i a : Fin m → kˣ) j : k))) =
          (Pi.mulSingle i (a : k) : Fin m → k) := by
      ext j
      by_cases hij : j = i <;> simp [hij]
    rw [hcoe]
    exact isElementaryMatrix_coordinateLinearBlock (k := k) m i (a : k) a.ne_zero

omit [IsAlgClosed k] in
private lemma transvection_nonsing_inv {m : ℕ}
    (t : Matrix.TransvectionStruct (Fin m) k) :
    t.toMatrix⁻¹ = Matrix.transvection t.i t.j (-t.c) := by
  calc
    t.toMatrix⁻¹ = t.inv.toMatrix := Matrix.inv_eq_left_inv (Matrix.TransvectionStruct.inv_mul t)
    _ = Matrix.transvection t.i t.j (-t.c) := rfl

private lemma isElementaryMatrix_linearBlock_transvection
    (m : ℕ) (t : Matrix.TransvectionStruct (Fin m) k) :
    IsElementaryMatrix (k := k) m (linearBlock m t.toMatrix) := by
  rcases lt_or_gt_of_ne t.hij with hij | hji
  · let r : TypeCRootIndex m := .inl
      ⟨⟨⟨t.i, t.j⟩, hij⟩, positiveRootSign, negativeRootSign⟩
    have hroot := isElementaryMatrix_root (k := k) m r t.c
    norm_num [r, symplecticRootMatrix, positiveRootSign, negativeRootSign] at hroot
    rw [linearBlock, transvection_nonsing_inv]
    simpa [Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
      Matrix.transpose_add, Matrix.transpose_single, symplecticSingle,
      sub_eq_add_neg, Matrix.single_neg] using hroot
  · let r : TypeCRootIndex m := .inl
      ⟨⟨⟨t.j, t.i⟩, hji⟩, negativeRootSign, positiveRootSign⟩
    have hroot := isElementaryMatrix_root (k := k) m r t.c
    norm_num [r, symplecticRootMatrix, positiveRootSign, negativeRootSign] at hroot
    rw [linearBlock, transvection_nonsing_inv]
    simpa [Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
      Matrix.transpose_add, Matrix.transpose_single, symplecticSingle,
      sub_eq_add_neg, Matrix.single_neg] using hroot

private lemma isElementaryMatrix_linearBlock
    (m : ℕ) (A : Matrix (Fin m) (Fin m) k) (hA : A.det ≠ 0) :
    IsElementaryMatrix (k := k) m (linearBlock m A) := by
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (P := fun B => IsElementaryMatrix (k := k) m (linearBlock m B)) A hA
  · exact isElementaryMatrix_linearBlock_diagonal (k := k) m
  · exact isElementaryMatrix_linearBlock_transvection (k := k) m
  · intro B C hB hC hBel hCel
    rw [linearBlock_mul]
    exact hBel.mul hCel

omit [IsAlgClosed k] in
private lemma exists_symmetric_pivot_of_ker_inter_eq_bot {m : ℕ}
    {A C : Matrix (Fin m) (Fin m) k}
    (hker : ∀ x : Fin m → k, A • x = 0 → C • x = 0 → x = 0)
    (hsymm : A.transpose * C = C.transpose * A) :
    ∃ X : Matrix (Fin m) (Fin m) k, X.IsSymm ∧ IsUnit (A + X * C) := by
  classical
  rcases Matrix.exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def
  set Q := V.transpose⁻¹ * A * U with Q_def
  set f := fun x : Matrix (Fin m) (Fin m) k => x.submatrix s.symm s.symm
  have hf (x : Matrix (Fin m) (Fin m) k) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x : Matrix (Fin m) (Fin m) k} : IsUnit x → IsUnit (f x) :=
    (Matrix.isUnit_submatrix_equiv ..).2
  have f_mul (x y : Matrix (Fin m) (Fin m) k) : f (x * y) = f x * f y :=
    Matrix.submatrix_mul _ _ _ _ _ s.symm.bijective
  letI : Invertible V := hV.invertible
  letI : Invertible U := hU.invertible
  letI : Invertible (f V.transpose) :=
    (f_unit (V.isUnit_transpose.2 hV)).invertible
  have con1 (x : Fin C.rank ⊕ Fin (Fintype.card (Fin m) - C.rank) → k)
      (heq1 : f Q • x = 0) (heq2 : f P • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero,
      mul_smul, hf, smul_eq_mulVec, submatrix_mulVec_equiv,
      Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
      exact s.surjective.injective_comp_right <| by simpa using hker _ heq1 heq2
    · exact f_unit hV
    · exact f_unit <| isUnit_nonsing_inv_iff.2 <|
        V.isUnit_transpose.2 hV
  have con2 : Q.transpose * P = P.transpose * Q := by
    simp only [P_def, Matrix.mul_assoc, Matrix.transpose_mul,
      Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Q_def,
      Matrix.inv_mul_cancel_left_of_invertible,
      Matrix.mul_inv_cancel_left_of_invertible]
    rw [← Matrix.mul_assoc A.transpose, hsymm, Matrix.mul_assoc]
  replace con2 : (f Q).toBlocks₁₁.transpose = (f Q).toBlocks₁₁ ∧
      (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Pᵀ,
      heq, hf, ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks,
      hf (_)ᵀ, hf ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] at con2
    tauto
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun x hx => Sum.elim_injective' <|
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]
      simp [hx, con2.2, Matrix.fromBlocks_mulVec]
    · simp [hf, heq, Matrix.fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card (Fin m) - C.rank))
      (Fin C.rank ⊕ Fin (Fintype.card (Fin m) - C.rank)) k :=
    Matrix.fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def, Matrix.isSymm_fromBlocks_iff]
    exact ⟨Matrix.IsSymm.sub Matrix.isSymm_one con2.1, by simp⟩
  set X := f V.transpose * Y * f V with X_def
  refine ⟨X.submatrix s s, Matrix.IsSymm.submatrix ?_ s,
    (Matrix.isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, Matrix.transpose_mul, hY_symm.eq, hf,
      Matrix.transpose_submatrix, Matrix.transpose_transpose, Matrix.mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) =
        f V.transpose * (f Q + Y * f P) * f U⁻¹ := by
      simp_rw [hf, Matrix.submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf,
        Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.inv_submatrix_equiv,
        Matrix.add_mul, Matrix.mul_assoc _ (U.submatrix _ _),
        Matrix.mul_inv_of_invertible]
      simp [X_def]
      rfl
    rw [← hf, heq', IsUnit.mul_iff, IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    · exact f_unit <| Matrix.isUnit_nonsing_inv_iff.2 hU

omit [IsAlgClosed k] in
private lemma exists_symmetric_pivot {m : ℕ}
    (M : SymplecticMatrix (k := k) m)
    (hM : M ∈ Matrix.symplecticGroup (Fin m) k) :
    ∃ X : Matrix (Fin m) (Fin m) k, X.IsSymm ∧
      IsUnit (M.toBlocks₁₁ + X * M.toBlocks₂₁) := by
  classical
  have hMunit : IsUnit M :=
    M.isUnit_iff_isUnit_det.2 (SymplecticGroup.symplectic_det hM)
  have hker (x : Fin m → k)
      (hx1 : M.toBlocks₁₁ • x = 0)
      (hx2 : M.toBlocks₂₁ • x = 0) : x = 0 := by
    rw [smul_eq_mulVec] at hx1 hx2
    have hv0 : M • Sum.elim x (0 : Fin m → k) =
        M • Sum.elim (0 : Fin m → k) (0 : Fin m → k) := by
      rw [← M.fromBlocks_toBlocks]
      simp [Matrix.fromBlocks_mulVec, hx1, hx2]
    exact (Sum.elim_eq_iff.1 (Matrix.mulVec_injective_iff_isUnit.2 hMunit hv0)).1
  exact exists_symmetric_pivot_of_ker_inter_eq_bot hker
    (SymplecticGroup.fromBlocks_mem_iff.1 (M.fromBlocks_toBlocks ▸ hM)).1

omit [IsAlgClosed k] in
private lemma symplectic_first_row_relation {m : ℕ}
    (M : SymplecticMatrix (k := k) m)
    (hM : M ∈ Matrix.symplecticGroup (Fin m) k) :
    M.toBlocks₁₁ * M.toBlocks₁₂.transpose =
      M.toBlocks₁₂ * M.toBlocks₁₁.transpose := by
  have hMT := SymplecticGroup.transpose_mem hM
  have hblocks := SymplecticGroup.fromBlocks_mem_iff.1
    (M.transpose.fromBlocks_toBlocks ▸ hMT)
  have h11 : M.transpose.toBlocks₁₁ = M.toBlocks₁₁.transpose := by
    ext i j
    rfl
  have h21 : M.transpose.toBlocks₂₁ = M.toBlocks₁₂.transpose := by
    ext i j
    rfl
  rw [h11, h21, Matrix.transpose_transpose] at hblocks
  simpa using hblocks.1

private lemma isElementaryMatrix_of_invertible_firstBlock {m : ℕ}
    (M : SymplecticMatrix (k := k) m)
    (hM : M ∈ Matrix.symplecticGroup (Fin m) k)
    (hA : M.toBlocks₁₁.det ≠ 0) :
    IsElementaryMatrix (k := k) m M := by
  let A := M.toBlocks₁₁
  let B := M.toBlocks₁₂
  let C := M.toBlocks₂₁
  let D := M.toBlocks₂₂
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hATu : IsUnit A.transpose.det := by
    simpa [Matrix.det_transpose] using hAu
  have hblocks := SymplecticGroup.fromBlocks_mem_iff.1
    (M.fromBlocks_toBlocks ▸ hM)
  have hAC : A.transpose * C = C.transpose * A := by
    simpa [A, C] using hblocks.1
  have hAB : A * B.transpose = B * A.transpose := by
    simpa [A, B] using symplectic_first_row_relation M hM
  have hAD : A.transpose * D = 1 + C.transpose * B := by
    exact sub_eq_iff_eq_add.mp (by simpa [A, B, C, D] using hblocks.2.2)
  let L := C * A⁻¹
  let U := A⁻¹ * B
  have hL : L.IsSymm := by
    change (C * A⁻¹).transpose = C * A⁻¹
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    have h := congrArg (fun Z => A.transpose⁻¹ * Z * A⁻¹) hAC
    simpa only [Matrix.nonsing_inv_mul_cancel_left A.transpose C hATu,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAu, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_right A (A.transpose⁻¹ * C.transpose) hAu]
      using h.symm
  have hU : U.IsSymm := by
    change (A⁻¹ * B).transpose = A⁻¹ * B
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    have h := congrArg (fun Z => A⁻¹ * Z * A.transpose⁻¹) hAB
    simpa only [Matrix.nonsing_inv_mul_cancel_left A B.transpose hAu,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv A.transpose hATu, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_right A.transpose (A⁻¹ * B) hATu]
      using h
  have hLC : A.transpose⁻¹ * C.transpose = C * A⁻¹ := by
    simpa [L, Matrix.transpose_mul, Matrix.transpose_nonsing_inv] using hL.eq
  have hD : D = A⁻¹.transpose + (C * A⁻¹) * B := by
    calc
      D = A.transpose⁻¹ * (A.transpose * D) := by
        symm
        exact Matrix.nonsing_inv_mul_cancel_left A.transpose D hATu
      _ = A.transpose⁻¹ * (1 + C.transpose * B) := by rw [hAD]
      _ = A.transpose⁻¹ + (A.transpose⁻¹ * C.transpose) * B := by
        noncomm_ring
      _ = A⁻¹.transpose + (C * A⁻¹) * B := by
        rw [hLC, Matrix.transpose_nonsing_inv]
  have hAU : A * U = B := by
    change A * (A⁻¹ * B) = B
    exact Matrix.mul_nonsing_inv_cancel_left A B hAu
  have hLA : L * A = C := by
    change C * A⁻¹ * A = C
    exact Matrix.nonsing_inv_mul_cancel_right A C hAu
  have hCU : C * U = (C * A⁻¹) * B := by
    simp [U, Matrix.mul_assoc]
  have hfactor : M = lowerUnipotent m L * linearBlock m A * upperUnipotent m U := by
    rw [← M.fromBlocks_toBlocks]
    change Matrix.fromBlocks A B C D =
      lowerUnipotent m L * linearBlock m A * upperUnipotent m U
    simp [lowerUnipotent, linearBlock, upperUnipotent,
      Matrix.fromBlocks_multiply, hAU, hLA, hCU, hD, Matrix.mul_assoc, add_comm]
  rw [hfactor]
  exact ((isElementaryMatrix_lower (k := k) m L hL).mul
    (isElementaryMatrix_linearBlock (k := k) m A hA)).mul
      (isElementaryMatrix_upper (k := k) m U hU)

omit [IsAlgClosed k] in
private lemma upperUnipotent_mem_symplectic {m : ℕ}
    (X : Matrix (Fin m) (Fin m) k) (hX : X.IsSymm) :
    upperUnipotent m X ∈ Matrix.symplecticGroup (Fin m) k := by
  rw [upperUnipotent, SymplecticGroup.fromBlocks_mem_iff]
  simp [hX.eq]

private lemma isElementaryMatrix_of_symplectic {m : ℕ}
    (M : SymplecticMatrix (k := k) m)
    (hM : M ∈ Matrix.symplecticGroup (Fin m) k) :
    IsElementaryMatrix (k := k) m M := by
  obtain ⟨X, hX, hPivot⟩ := exists_symmetric_pivot M hM
  let N := upperUnipotent m X * M
  have hN : N ∈ Matrix.symplecticGroup (Fin m) k :=
    (Matrix.symplecticGroup (Fin m) k).mul_mem
      (upperUnipotent_mem_symplectic (k := k) X hX) hM
  have hN11 : N.toBlocks₁₁ = M.toBlocks₁₁ + X * M.toBlocks₂₁ := by
    change (upperUnipotent m X * M).toBlocks₁₁ =
      M.toBlocks₁₁ + X * M.toBlocks₂₁
    rw [← M.fromBlocks_toBlocks]
    simp [upperUnipotent, Matrix.fromBlocks_multiply]
  have hNunit : IsUnit N.toBlocks₁₁ := by
    rwa [hN11]
  have hNdet : N.toBlocks₁₁.det ≠ 0 :=
    (N.toBlocks₁₁.isUnit_iff_isUnit_det.mp hNunit).ne_zero
  have hNel := isElementaryMatrix_of_invertible_firstBlock N hN hNdet
  have hneg : (-X).IsSymm := hX.neg
  have hcancel : upperUnipotent m (-X) * upperUnipotent m X = 1 := by
    rw [← upperUnipotent_add]
    simp [upperUnipotent_zero]
  have hfactor : M = upperUnipotent m (-X) * N := by
    simp [N, ← Matrix.mul_assoc, hcancel]
  rw [hfactor]
  exact (isElementaryMatrix_upper (k := k) m (-X) hneg).mul hNel

public theorem standardSymplectic_rootSubgroups_generate (m : ℕ) :
    Subgroup.closure (⋃ r : TypeCRootIndex m,
      (symplecticRootSubgroup (k := k) m r : Set (Variety.Point
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety))) = ⊤ := by
  change symplecticRootGenerated (k := k) m = ⊤
  apply top_unique
  intro g _
  obtain ⟨x, hx, hmatrix⟩ := isElementaryMatrix_of_symplectic
    (symplecticClosedPointMatrix m g) (symplecticClosedPointMatrix_mem m g)
  have hxg : x = g := symplecticClosedPointMatrix_injective m hmatrix
  simpa [hxg] using hx

private lemma symplecticRootSubgroup_isConnected (m : ℕ) (r : TypeCRootIndex m) :
    _root_.IsConnected
      (symplecticRootSubgroup (k := k) m r : Set (SymplecticPoint (k := k) m)) := by
  let X := symplecticRootSubgroup (k := k) m r
  letI : AlgebraicGroup X.carrierVariety := X.carrierAlgebraicGroup
  let : ConnectedSpace (Variety.Point X.carrierVariety) :=
    connectedSpace_iff_univ.mpr (symplecticRootSubgroup_isOneParameter m r).isConnected
  change _root_.IsConnected (X.toSubgroup : Set (SymplecticPoint (k := k) m))
  rw [← X.range_inclusion]
  exact isConnected_range X.inclusion.toVariety.continuous

public theorem standardSymplecticClosedSubgroup_isConnected (m : ℕ) :
    Variety.IsConnected
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety := by
  let H : TypeCRootIndex m →
      ClosedSubgroup (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
    fun r => symplecticRootSubgroup m r
  have hHconn : ∀ r, _root_.IsConnected
      (H r : Set (SymplecticPoint (k := k) m)) := by
    intro r
    exact symplecticRootSubgroup_isConnected m r
  have hclosed : IsZariskiClosed
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety
      (symplecticRootGenerated (k := k) m : Set (SymplecticPoint (k := k) m)) := by
    exact closure_iUnion_connected_closedSubgroup_isZariskiClosed H hHconn
  let C : ClosedSubgroup
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
    ClosedSubgroup.ofSubgroup (symplecticRootGenerated (k := k) m) hclosed
  have hroot_le (r : TypeCRootIndex m) : H r ≤ C := by
    intro x hx
    change x ∈ symplecticRootGenerated (k := k) m
    exact Subgroup.subset_closure (Set.mem_iUnion_of_mem r hx)
  have hroot_component (r : TypeCRootIndex m) :
      H r ≤ C.identityComponentAmbient :=
    connected_closedSubgroup_le_identityComponentAmbient (H r) C
      (hHconn r) (hroot_le r)
  have hgenerated : symplecticRootGenerated (k := k) m ≤
      C.identityComponentAmbient.toSubgroup := by
    apply (Subgroup.closure_le C.identityComponentAmbient.toSubgroup).2
    rw [Set.iUnion_subset_iff]
    exact hroot_component
  have hcomponentTop : C.identityComponentAmbient.toSubgroup = ⊤ := by
    apply top_unique
    rw [← standardSymplectic_rootSubgroups_generate (k := k) m]
    exact hgenerated
  have hconn := C.identityComponentAmbient_isConnected
  change _root_.IsConnected
    (C.identityComponentAmbient.toSubgroup : Set (SymplecticPoint (k := k) m)) at hconn
  rw [hcomponentTop] at hconn
  have hcarrier : _root_.IsConnected
      (Set.univ : Set (SymplecticPoint (k := k) m)) := by
    simpa only [Subgroup.coe_top] using hconn
  let : ConnectedSpace (SymplecticPoint (k := k) m) :=
    connectedSpace_iff_univ.mpr hcarrier
  exact connectedSpace_iff_univ.mp inferInstance

end Theory.AlgebraicGroup
