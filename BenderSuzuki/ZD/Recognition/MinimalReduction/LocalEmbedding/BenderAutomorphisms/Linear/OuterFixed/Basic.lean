module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.FieldAction
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.FieldTheory.Fixed
public import Mathlib.Algebra.Ring.Action.End

/-!
# Semilinear involution identities and exact field fixed groups

Conjugation preserves trace, and SL₂ contains matrices of every trace. Thus a
field automorphism inducing an inner automorphism is trivial. Squaring an
explicit semilinear involution consequently gives both an involutory field
automorphism and the matrix cocycle identity; the center vanishes in
characteristic two.

The entrywise fixed subgroup is identified with SL₂ over the actual fixed
subfield, by constructing the inverse on every fixed matrix. Transport through
the characteristic-two quotient equivalence gives the corresponding PSL₂
statement, including over GF(2).

These are steps toward GLS, Volume 4, Chapter 4, Lemma 3.4(c). Trivialization of
the semilinear cocycle is a separate mathematical input.
-/

namespace BenderSuzuki.ZD.Linear
open Matrix BenderSuzuki.MatrixGroups
variable {K : Type*} [Field K]

public theorem sl2FieldAut_eq_conj_implies_refl (σ : K ≃+* K)
    (g : SpecialLinearGroup (Fin 2) K) (h : sl2FieldAut σ = MulAut.conj g) :
    σ = RingEquiv.refl K := by
  ext t
  let x : SpecialLinearGroup (Fin 2) K := ⟨!![t, -1; 1, 0], by simp⟩
  have hx := congrArg (fun a : MulAut (SpecialLinearGroup (Fin 2) K) =>
    Matrix.trace (a x).val) h
  have hc : Matrix.trace (g * x * g⁻¹).val = Matrix.trace x.val := by
    let c := SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := K)
    change Matrix.trace (c (g * x * g⁻¹)) = Matrix.trace (c x)
    rw [map_mul, map_mul, Matrix.trace_mul_cycle, ← map_mul, inv_mul_cancel,
      map_one, one_mul]
  change Matrix.trace (sl2FieldAut σ x).val = Matrix.trace (g * x * g⁻¹).val at hx
  rw [hc] at hx
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hx
  change σ t + σ 0 = t + 0 at hx
  simpa using hx

variable [CharP K 2]
public theorem fieldAut_eq_conj_implies_refl (σ : K ≃+* K) (g : PSL2MatrixGroup K)
    (h : fieldAut σ = MulAut.conj g) : σ = RingEquiv.refl K := by
  apply sl2FieldAut_eq_conj_implies_refl σ ((sl2QuotientEquiv K).symm g)
  apply (MulAut.congr (sl2QuotientEquiv K)).injective
  rw [MulAut.congr_conj, MulEquiv.apply_symm_apply]
  exact h

public theorem fieldAut_refl : fieldAut (RingEquiv.refl K) = 1 := by
  have h : sl2FieldAut (RingEquiv.refl K) = 1 := by ext g i j; rfl
  change MulAut.congr (sl2QuotientEquiv K) _ = 1
  rw [h, map_one]

public theorem fieldAut_trans (σ τ : K ≃+* K) :
    fieldAut (τ.trans σ) = fieldAut σ * fieldAut τ := by
  have h : sl2FieldAut (τ.trans σ) = sl2FieldAut σ * sl2FieldAut τ := by
    ext g i j; rfl
  change MulAut.congr (sl2QuotientEquiv K) _ = _
  rw [h, map_mul]
  rfl

public theorem conj_field_square (σ : K ≃+* K) (g : PSL2MatrixGroup K) :
    (MulAut.conj g * fieldAut σ) ^ 2 =
      MulAut.conj (g * fieldAut σ g) * fieldAut (σ.trans σ) := by
  rw [fieldAut_trans]
  ext x
  simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

public theorem psl2_conj_eq_one_implies (g : PSL2MatrixGroup K) (h : MulAut.conj g = 1) :
    g = 1 := by
  let e := sl2QuotientEquiv K
  have hc : e.symm g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply e.injective
    have hx := DFunLike.congr_fun h (e x)
    change g * e x * g⁻¹ = e x at hx
    simpa using (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hz : e.symm g = 1 := by
    have hb := (le_of_eq (Converse.center_SL2_eq_bot (F := K))) hc
    exact hb
  clear hc
  simpa using congrArg e hz

public theorem semilinear_involution_data (σ : K ≃+* K) (g : PSL2MatrixGroup K)
    (h : (MulAut.conj g * fieldAut σ) ^ 2 = 1) :
    Function.Involutive σ ∧ g * fieldAut σ g = 1 := by
  rw [conj_field_square] at h
  have hf : fieldAut (σ.trans σ) = (MulAut.conj (g * fieldAut σ g))⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  have hs := fieldAut_eq_conj_implies_refl (σ.trans σ) (g * fieldAut σ g)⁻¹ (by
    simpa only [map_inv] using hf)
  refine ⟨fun x => DFunLike.congr_fun hs x, ?_⟩
  rw [hs, fieldAut_refl, mul_one] at h
  exact psl2_conj_eq_one_implies _ h

public noncomputable def sl2FixedEquiv (σ : K ≃+* K) :
    (sl2FieldAut σ).fixedSubgroup ≃*
      SpecialLinearGroup (Fin 2) (FixedBy.subfield K σ) := by
  let F := FixedBy.subfield K σ
  let φ := SpecialLinearGroup.map F.subtype (n := Fin 2)
  have hφ (A : SpecialLinearGroup (Fin 2) F) : φ A ∈ (sl2FieldAut σ).fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    ext i j
    exact (A.val i j).property
  let ψ := φ.codRestrict (sl2FieldAut σ).fixedSubgroup hφ
  apply (MulEquiv.ofBijective ψ ?_).symm
  constructor
  · intro A B h
    have hm : φ A = φ B := congrArg Subtype.val h
    apply Subtype.ext
    ext i j
    exact congrArg (fun M : SpecialLinearGroup (Fin 2) K => M.val i j) hm
  · intro A
    have hf (i j : Fin 2) : σ (A.val i j) = A.val i j :=
      congrArg (fun M : SpecialLinearGroup (Fin 2) K => M i j)
        ((MulAut.mem_fixedSubgroup _ _).mp A.property)
    let Dmat : Matrix (Fin 2) (Fin 2) F := fun i j => ⟨A.val i j, hf i j⟩
    let D : SpecialLinearGroup (Fin 2) F := ⟨Dmat, by
      apply F.subtype.injective
      change F.subtype Dmat.det = 1
      exact (F.subtype.map_det Dmat).trans A.val.property⟩
    exact ⟨D, Subtype.ext (by rfl)⟩

public noncomputable def fieldAutFixedEquiv (σ : K ≃+* K) :
    (fieldAut σ).fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield K σ) :=
  (MulAut.fixedSubgroupCongr (sl2QuotientEquiv K) (sl2FieldAut σ)).symm.trans
    ((sl2FixedEquiv σ).trans (sl2QuotientEquiv _))
end BenderSuzuki.ZD.Linear
