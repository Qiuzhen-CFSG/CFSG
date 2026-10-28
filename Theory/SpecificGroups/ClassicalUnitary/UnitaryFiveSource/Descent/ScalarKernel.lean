module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.Conjugation
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.CharP.Two
public import Theory.FieldTheory.RootsOfUnityCard

/-!
# The projective centralizer of PSU₅(4)

A projective commutation relation with a matrix of nonzero trace lifts to
matrix commutation. Determinant-one fifth-root diagonal matrices have
nonzero trace and separate each pair of coordinate positions. They force
a projective centralizer matrix to be diagonal. Coordinate swaps have
trace one in characteristic two and force its diagonal entries to agree.
Thus the centralizer is scalar before passing to PGL.

This is the scalar-kernel step for the graph descent in F.4.29(2), printed
p.289 of refs/quasithin.pdf. The trace argument is adapted from
SU3/ProjectiveOuterInvolutions/Descent/ScalarKernel.lean; the fifth-root
and five-dimensional coordinate calculations are specific to this carrier.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.Descent
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem commute_of_projective_commute_of_trace_ne_zero
    (A X : GL (Fin 5) F) (hX : X.val.trace ≠ 0)
    (h : Commute (ProjGenLinGroup.mk A) (ProjGenLinGroup.mk X)) : Commute A X := by
  have hp : ProjGenLinGroup.mk (A * X * A⁻¹) = ProjGenLinGroup.mk X := by
    simpa only [map_mul, map_inv] using (mul_inv_eq_iff_eq_mul).mpr h.eq
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have ht := congrArg (fun B : GL (Fin 5) F => B.val.trace) hc
  have hm : ((A * X * A⁻¹) * GeneralLinearGroup.scalar (Fin 5) c).val =
      (c : F) • (A.val * X.val * (A⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  rw [hm, trace_smul, trace_units_conj] at ht
  have hc1 : c = 1 := Units.ext (mul_right_cancel₀ hX (ht.trans (one_mul _).symm))
  rw [hc1, map_one, mul_one] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc : A * X = X * A)

private def diagonalGL (d : Fin 5 → Fˣ) : GL (Fin 5) F where
  val := diagonal (fun i => (d i : F))
  inv := diagonal (fun i => ((d i)⁻¹ : Fˣ))
  val_inv := by ext i j; by_cases h : i=j <;> simp [h,Matrix.one_apply]
  inv_val := by ext i j; by_cases h : i=j <;> simp [h,Matrix.one_apply]

omit [CharP F 2] in
private theorem root_conj_mul (hconj : ∀ x, J.conj x=x^4) (t : rootsOfUnity 5 F) :
    J.conj (t.val : F) * (t.val : F)=1 := by
  rw [hconj,←pow_succ]
  exact (mem_rootsOfUnity' 5 t.val).mp t.property

private def diagonalSpecial (hJ : J.form=1) (hconj : ∀ x, J.conj x=x^4)
    (d : Fin 5 → rootsOfUnity 5 F) (hd : ∏ i, d i=1) : J.specialSubgroup :=
  ⟨diagonalGL (fun i => (d i).val),by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · rw [hJ]
      change J.conjTranspose (diagonal (fun i => ((d i).val : F))) * 1 *
        diagonal (fun i => ((d i).val : F))=1
      have ha : J.conjTranspose (diagonal (fun i => ((d i).val : F))) =
          diagonal (fun i => J.conj ((d i).val : F)) := by
        ext i j
        by_cases h : i=j
        · subst j; simp [HermitianForm.conjTranspose]
        · simp [HermitianForm.conjTranspose,h,Ne.symm h]
      rw [ha,mul_one,diagonal_mul_diagonal]
      ext i j
      by_cases h : i=j
      · subst j; simp only [diagonal_apply_eq,one_apply_eq]; exact root_conj_mul J hconj _
      · simp [h]
    · apply Units.ext
      rw [GeneralLinearGroup.val_det_apply,Units.val_one]
      change (diagonal (fun i => ((d i).val : F))).det=1
      rw [det_diagonal]
      calc
        ∏ i, ((d i).val : F) = ((∏ i, d i).val : F) := by
          simp
        _ = 1 := by rw [hd]; rfl⟩

private def phase (hJ : J.form=1) (hconj : ∀ x, J.conj x=x^4)
    (t : rootsOfUnity 5 F) (i j : Fin 5) : J.specialSubgroup :=
  diagonalSpecial J hJ hconj (Pi.mulSingle i t * Pi.mulSingle j t⁻¹) (by
    simp [Finset.prod_mul_distrib])

private theorem phase_trace (hJ : J.form=1) (hconj : ∀ x, J.conj x=x^4)
    (t : rootsOfUnity 5 F) (ht : t≠1) (i j : Fin 5) (hij : i≠j) :
    (phase J hJ hconj t i j).val.val.trace ≠ 0 := by
  have ht0 : (t.val : F) ≠ 0 := t.val.ne_zero
  have ht1 : (t.val : F) ≠ 1 := fun h => ht (Subtype.ext (Units.ext h))
  have hp : (t.val : F)^5=1 := (mem_rootsOfUnity' 5 t.val).mp t.property
  have htr : (phase J hJ hconj t i j).val.val.trace=
      (t.val : F) + (t.val : F)⁻¹ + 1 := by
    change (diagonal _).trace=_
    rw [trace_diagonal]
    fin_cases i <;> fin_cases j <;>
      simp [Pi.mulSingle_apply,Fin.sum_univ_succ,add_assoc,add_left_comm,add_comm,
        CharTwo.add_self_eq_zero] at hij ⊢
  rw [htr]
  intro h
  have hpoly : (t.val : F)^2+(t.val : F)+1=0 := by
    have hh := congrArg (fun a : F => a*(t.val : F)) h
    rw [add_mul,add_mul,inv_mul_cancel₀ ht0,one_mul,zero_mul] at hh
    linear_combination hh
  have h3 : (t.val : F)^3=1 := by
    linear_combination ((t.val : F)-1)*hpoly
  apply ht1
  calc
    (t.val : F) = ((t.val : F)^3)^2 / (t.val : F)^5 := by field_simp
    _ = 1 := by rw [h3,hp]; simp

private def swapGL (i j : Fin 5) : GL (Fin 5) F where
  val := (Equiv.swap i j).permMatrix F
  inv := (Equiv.swap i j).permMatrix F
  val_inv := by rw [← permMatrix_mul]; simp
  inv_val := by rw [← permMatrix_mul]; simp

private def swapSpecial (hJ : J.form=1) (i j : Fin 5) : J.specialSubgroup :=
  ⟨swapGL i j,by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · have hc : ((Equiv.swap i j).permMatrix F).map J.conj =
          (Equiv.swap i j).permMatrix F := by
        ext a b
        simp [Equiv.Perm.permMatrix,PEquiv.toMatrix]
      change (((Equiv.swap i j).permMatrix F).map J.conj).transpose * J.form *
        (Equiv.swap i j).permMatrix F = J.form
      rw [hc,hJ,mul_one,transpose_permMatrix]
      rw [← permMatrix_mul]
      simp
    · apply Units.ext
      rw [GeneralLinearGroup.val_det_apply,Units.val_one]
      change ((Equiv.swap i j).permMatrix F).det=1
      rw [det_permutation,Equiv.Perm.sign_swap']
      split_ifs <;> simp [CharTwo.neg_eq]⟩

private theorem swap_trace (hJ : J.form=1) (i j : Fin 5) :
    (swapSpecial J hJ i j).val.val.trace ≠ 0 := by
  change ((Equiv.swap i j).permMatrix F).trace ≠ 0
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;>
    norm_num [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
      Equiv.swap_apply_def,Fin.ext_iff,CharTwo.add_self_eq_zero]

/-- The centralizer in PGL of the actual PSU₅(4) image is trivial. -/
theorem projective_centralizer_scalar [Finite F]
    (hJ : J.form=1) (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card F=16)
    (A : GL (Fin 5) F)
    (hA : ∀ b : ProjectiveSpecialUnitaryMatrixGroup J,
      Commute (ProjGenLinGroup.mk A) b.val) :
    A ∈ Subgroup.center (GL (Fin 5) F) := by
  classical
  have hr : Nat.card (rootsOfUnity 5 F)=5 :=
    FiniteField.card_rootsOfUnity_of_dvd F 5 (by rw [hcard]; decide)
  let := Fintype.ofFinite (rootsOfUnity 5 F)
  have hn : Nontrivial (rootsOfUnity 5 F) := Fintype.one_lt_card_iff_nontrivial.mp
    (by rw [← Nat.card_eq_fintype_card,hr]; decide)
  obtain ⟨t,ht⟩ := exists_ne (1 : rootsOfUnity 5 F)
  have ht1 : (t.val : F)≠1 := fun h => ht (Subtype.ext (Units.ext h))
  have hcomm (X : J.specialSubgroup) (htr : X.val.val.trace ≠ 0) :
      A.val * X.val.val = X.val.val * A.val :=
    congrArg Units.val
      (commute_of_projective_commute_of_trace_ne_zero A X.val htr
        (hA (project J X))).eq
  have hoff (i j : Fin 5) (hij : i≠j) : A.val i j=0 := by
    obtain ⟨k,hki,hkj⟩ : ∃ k : Fin 5, k≠i ∧ k≠j := by
      fin_cases i <;> fin_cases j <;> decide
    have hm := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j)
      (hcomm (phase J hJ hconj t i k) (phase_trace J hJ hconj t ht i k hki.symm))
    change (A.val * diagonal _ : Matrix (Fin 5) (Fin 5) F) i j =
      (diagonal _ * A.val : Matrix (Fin 5) (Fin 5) F) i j at hm
    simp only [mul_diagonal,diagonal_mul] at hm
    simp [hij.symm,hki.symm,hkj.symm] at hm
    exact (mul_eq_zero.mp (by linear_combination hm :
      (1-(t.val : F))*A.val i j=0)).resolve_left (sub_ne_zero.mpr ht1.symm)
  have heq (i j : Fin 5) : A.val i i=A.val j j := by
    by_cases hij : i=j
    · subst j; rfl
    have hm := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j)
      (hcomm (swapSpecial J hJ i j) (swap_trace J hJ i j))
    change (A.val * (Equiv.swap i j).toPEquiv.toMatrix : Matrix (Fin 5) (Fin 5) F) i j =
      ((Equiv.swap i j).toPEquiv.toMatrix * A.val : Matrix (Fin 5) (Fin 5) F) i j at hm
    rw [PEquiv.mul_toMatrix_toPEquiv,PEquiv.toMatrix_toPEquiv_mul] at hm
    simpa [Matrix.submatrix_apply] using hm
  apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  refine ⟨A.val 0 0, ?_⟩
  ext i j
  by_cases hij : i=j
  · subst j; simp [Matrix.scalar_apply,heq i 0]
  · simp [Matrix.scalar_apply,hij,hoff i j hij]

end Theory.SpecificGroups.UnitaryFive.Descent
