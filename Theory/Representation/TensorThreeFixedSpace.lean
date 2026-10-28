module

public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Theory.AlgebraicGroup.Representations.Semisimple
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic

/-!
# Fixed matrices for two odd three-dimensional factors

Over an algebraic closure an odd-order operator in characteristic two has
an eigenbasis. For two nonscalar triples, each row of unit eigenvalue pairs
has at most two entries; two unequal rows are disjoint and have at most
three entries between them. Thus there are at most five fixed coordinates.
Flat scalar extension transfers the bound to arbitrary binary fields and
to every injectively embedded space of fixed matrices.

The literal Hermitian congruence action consumes this calculation in
`Chapter8.Section02.HermitianSourceOddElements`, retaining its norm-one
scalar kernel. Source: Aschbacher–Smith, combined manuscript of 1 March
2004, the beta calculation in H.4.2, printed p.382 (refs/quasithin.pdf).
-/

public noncomputable section
open Module Matrix
open scoped Classical TensorProduct
namespace Representation.TensorThreeFixedSpace
variable {K : Type*} [Field K]

private theorem pair_count (a b : Fin 3 → K)
    (ha : ¬ ∃ c, ∀ i, a i = c) (hb : ¬ ∃ c, ∀ i, b i = c) :
    ∑ i : Fin 3, (Finset.univ.filter (fun j : Fin 3 => a i * b j = 1)).card ≤ 5 := by
  classical
  let R (i : Fin 3) := Finset.univ.filter (fun j : Fin 3 => a i * b j = 1)
  have hr (i : Fin 3) : (R i).card ≤ 2 := by
    have hh : (R i).card < (Finset.univ : Finset (Fin 3)).card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro he
      have hmul (j : Fin 3) : a i * b j = 1 := by
        have hj : j ∈ R i := he ▸ Finset.mem_univ j
        exact (Finset.mem_filter.mp hj).2
      have hi : a i ≠ 0 := by intro h; simpa [h] using hmul 0
      exact hb ⟨b 0, fun j => mul_left_cancel₀ hi ((hmul j).trans (hmul 0).symm)⟩
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.lt_succ_iff] using hh
  obtain ⟨i,j,hij⟩ : ∃ i j, a i ≠ a j := by
    by_contra h
    push Not at h
    exact ha ⟨a 0, fun i => h i 0⟩
  have hne : i ≠ j := fun he => hij (he ▸ rfl)
  have hd : Disjoint (R i) (R j) := by
    apply Finset.disjoint_left.mpr
    intro k hi hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have hk : b k ≠ 0 := by intro h; simp [h] at hi'
    exact hij (mul_right_cancel₀ hk (hi'.trans hj'.symm))
  have hp : (R i).card + (R j).card ≤ 3 := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin 3)
  change ∑ k : Fin 3, (R k).card ≤ 5
  rw [Fin.sum_univ_three]
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk] at hp hne <;> omega

/-- A matrix space supported on the unit eigenvalues of two nonconstant triples
has dimension at most five. -/
theorem finrank_le_five_of_coordinates
    {W : Type*} [AddCommGroup W] [Module K W]
    (f : W →ₗ[K] Matrix (Fin 3) (Fin 3) K) (hf : Function.Injective f)
    (a b : Fin 3 → K) (ha : ¬ ∃ c, ∀ i, a i = c) (hb : ¬ ∃ c, ∀ i, b i = c)
    (hfix : ∀ w i j, a i * b j * f w i j = f w i j) :
    finrank K W ≤ 5 := by
  classical
  let S := {p : Fin 3 × Fin 3 | a p.1 * b p.2 = 1}
  let c : W →ₗ[K] (S → K) :=
    { toFun := fun w p => f w p.val.1 p.val.2
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hc : Function.Injective c := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro w hw
    apply hf
    rw [map_zero]
    ext i j
    by_cases hp : a i * b j = 1
    · exact congrFun hw ⟨(i,j),hp⟩
    · have hz : (a i * b j - 1) * f w i j = 0 := by
        rw [sub_mul, one_mul, hfix, sub_self]
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hp)
  have hd := LinearMap.finrank_le_finrank_of_injective hc
  have hs : Fintype.card S = ∑ i : Fin 3,
      (Finset.univ.filter (fun j : Fin 3 => a i * b j = 1)).card := by
    let e : S ≃ (Σ i : Fin 3, {j : Fin 3 // a i * b j = 1}) :=
      { toFun := fun p => ⟨p.val.1, p.val.2, p.property⟩
        invFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩ }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [Fintype.card_subtype]
  rw [Module.finrank_pi, hs] at hd
  exact hd.trans (pair_count a b ha hb)

/-- The eigenvalue count applies to the literal kernel, without presupposing
its dimension or a classification of the eigenvalues. -/
theorem finrank_ker_le_five_of_eigenbasis
    {W : Type*} [AddCommGroup W] [Module K W]
    (T : Module.End K W) (c : Basis (Fin 3 × Fin 3) K W)
    (a b : Fin 3 → K) (ha : ¬ ∃ t, ∀ i, a i = t) (hb : ¬ ∃ t, ∀ i, b i = t)
    (hT : ∀ i j, T (c (i,j)) = (a i * b j) • c (i,j)) :
    finrank K (LinearMap.ker (T - 1)) ≤ 5 := by
  let f : LinearMap.ker (T - 1) →ₗ[K] Matrix (Fin 3) (Fin 3) K :=
    { toFun := fun w i j => c.repr w.val (i,j)
      map_add' := by intros; ext; simp only [Submodule.coe_add, map_add, Finsupp.add_apply]; rfl
      map_smul' := by intros; ext; simp only [Submodule.coe_smul, map_smul, Finsupp.smul_apply]; rfl }
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply c.repr.injective
    ext ⟨i,j⟩
    exact congrFun (congrFun he i) j
  apply finrank_le_five_of_coordinates f hf a b ha hb
  intro w i j
  have he : (c.coord (i,j)).comp T = (a i * b j) • c.coord (i,j) := by
    apply c.ext
    intro p
    rcases p with ⟨k,l⟩
    simp only [LinearMap.comp_apply, hT, map_smul, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_apply, LinearMap.smul_apply, smul_eq_mul]
    by_cases hp : (k,l) = (i,j)
    · cases hp; rfl
    · simp [hp]
  have hw : T w.val = w.val := sub_eq_zero.mp w.property
  have hh := LinearMap.congr_fun he w.val
  rw [LinearMap.comp_apply, hw] at hh
  exact hh.symm

open Theory.AlgebraicGroup in
/-- Two nonscalar semisimple factors of dimension three have at most five
fixed vectors in their nine-dimensional tensor product. -/
theorem tensor_fixed_finrank_le_five [IsAlgClosed K]
    (A B : Module.End K (Fin 3 → K))
    (hA : A.IsSemisimple) (hB : B.IsSemisimple)
    (ha : ¬ ∃ c : K, A = c • (1 : Module.End K (Fin 3 → K)))
    (hb : ¬ ∃ c : K, B = c • (1 : Module.End K (Fin 3 → K))) :
    finrank K (LinearMap.ker (TensorProduct.map A B - 1)) ≤ 5 := by
  obtain ⟨c,a,ha'⟩ : ∃ (c : Basis (Fin 3) K (Fin 3 → K)) (a : Fin 3 → K),
      ∀ i, A (c i) = a i • c i := by
    have hh := Module.End.IsSemisimple.exists_fin_eigenbasis A hA
    rw [Module.finrank_pi, Fintype.card_fin] at hh
    exact hh
  obtain ⟨d,b,hb'⟩ : ∃ (d : Basis (Fin 3) K (Fin 3 → K)) (b : Fin 3 → K),
      ∀ i, B (d i) = b i • d i := by
    have hh := Module.End.IsSemisimple.exists_fin_eigenbasis B hB
    rw [Module.finrank_pi, Fintype.card_fin] at hh
    exact hh
  have hna : ¬ ∃ t, ∀ i, a i = t := by
    rintro ⟨t,ht⟩
    apply ha
    refine ⟨t,c.ext fun i => ?_⟩
    simpa only [ht, LinearMap.smul_apply, Module.End.one_apply] using ha' i
  have hnb : ¬ ∃ t, ∀ i, b i = t := by
    rintro ⟨t,ht⟩
    apply hb
    refine ⟨t,d.ext fun i => ?_⟩
    simpa only [ht, LinearMap.smul_apply, Module.End.one_apply] using hb' i
  apply finrank_ker_le_five_of_eigenbasis (TensorProduct.map A B)
    (c.tensorProduct d) a b hna hnb
  intro i j
  simp only [Basis.tensorProduct_apply, TensorProduct.map_tmul, ha', hb',
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]


private def matrixTensorCoordinates :
    (Fin 3 → K) ⊗[K] (Fin 3 → K) ≃ₗ[K] Matrix (Fin 3) (Fin 3) K :=
  (TensorProduct.comm K _ _).trans (TensorProduct.piScalarRight K K (Fin 3 → K) (Fin 3))

private theorem matrixTensorCoordinates_tmul (x y : Fin 3 → K) :
    matrixTensorCoordinates (x ⊗ₜ[K] y) = Matrix.vecMulVec x y := rfl

private def matrixOperator (A B : Matrix (Fin 3) (Fin 3) K) :
    Module.End K (Matrix (Fin 3) (Fin 3) K) where
  toFun X := A * X * B.transpose
  map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' := by intros; simp

private theorem matrixTensorCoordinates_intertwines (A B : Matrix (Fin 3) (Fin 3) K)
    (u : (Fin 3 → K) ⊗[K] (Fin 3 → K)) :
    matrixTensorCoordinates (TensorProduct.map (Matrix.toLinAlgEquiv' A) (Matrix.toLinAlgEquiv' B) u) =
      matrixOperator A B (matrixTensorCoordinates u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul x y =>
    rw [TensorProduct.map_tmul, matrixTensorCoordinates_tmul, matrixTensorCoordinates_tmul]
    change Matrix.vecMulVec (A.mulVec x) (B.mulVec y) = A * Matrix.vecMulVec x y * B.transpose
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- The spectral bound on an arbitrary embedded space of fixed matrices. -/
theorem matrix_fixed_finrank_le_five [IsAlgClosed K]
    (A B : Matrix (Fin 3) (Fin 3) K)
    (hA : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' A)) (hB : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' B))
    (ha : ¬ ∃ c : K, A = c • 1) (hb : ¬ ∃ c : K, B = c • 1)
    {W : Type*} [AddCommGroup W] [Module K W]
    (f : W →ₗ[K] Matrix (Fin 3) (Fin 3) K) (hf : Function.Injective f)
    (hfix : ∀ w, A * f w * B.transpose = f w) : finrank K W ≤ 5 := by
  let A' := Matrix.toLinAlgEquiv' A
  let B' := Matrix.toLinAlgEquiv' B
  have ha' : ¬ ∃ c : K, A' = c • 1 := by
    rintro ⟨c,hc⟩
    apply ha
    refine ⟨c, Matrix.toLinAlgEquiv'.injective ?_⟩
    simpa only [map_smul, map_one] using hc
  have hb' : ¬ ∃ c : K, B' = c • 1 := by
    rintro ⟨c,hc⟩
    apply hb
    refine ⟨c, Matrix.toLinAlgEquiv'.injective ?_⟩
    simpa only [map_smul, map_one] using hc
  let T := TensorProduct.map A' B'
  let j := matrixTensorCoordinates.symm.toLinearMap.comp f
  let k : W →ₗ[K] LinearMap.ker (T - 1) := j.codRestrict _ (by
    intro w
    change T (j w) - j w = 0
    apply sub_eq_zero.mpr
    apply matrixTensorCoordinates.injective
    rw [matrixTensorCoordinates_intertwines]
    change matrixOperator A B (matrixTensorCoordinates (matrixTensorCoordinates.symm (f w))) =
      matrixTensorCoordinates (matrixTensorCoordinates.symm (f w))
    simpa only [LinearEquiv.apply_symm_apply, matrixOperator, LinearMap.coe_mk, AddHom.coe_mk] using hfix w)
  have hk : Function.Injective k := by
    intro v w h
    exact hf (matrixTensorCoordinates.symm.injective (congrArg Subtype.val h))
  exact (LinearMap.finrank_le_finrank_of_injective hk).trans
    (tensor_fixed_finrank_le_five A' B' hA hB ha' hb')

variable (K) in
private def matrixBaseChange (F : Type*) [Field F] [Algebra F K] :
    K ⊗[F] Matrix (Fin 3) (Fin 3) F ≃ₗ[K] Matrix (Fin 3) (Fin 3) K :=
  (TensorProduct.piRight F K K (fun _ : Fin 3 => Fin 3 → F)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.piScalarRight F K K (Fin 3))

set_option backward.isDefEq.respectTransparency false in
private theorem matrixBaseChange_tmul {F : Type*} [Field F] [Algebra F K]
    (a : K) (X : Matrix (Fin 3) (Fin 3) F) :
    matrixBaseChange K F (a ⊗ₜ[F] X) = a • X.map (algebraMap F K) := by
  ext i j
  change (TensorProduct.piScalarRight F K K (Fin 3))
    (((TensorProduct.piRight F K K (fun _ : Fin 3 => Fin 3 → F)) (a ⊗ₜ[F] X)) i) j = _
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  simp only [Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def]
  exact mul_comm _ _

theorem matrix_nonscalar_map {F : Type*} [Field F] (φ : F →+* K)
    (A : Matrix (Fin 3) (Fin 3) F) (ha : ¬ ∃ c : F, A = c • 1) :
    ¬ ∃ c : K, A.map φ = c • 1 := by
  rintro ⟨c,hc⟩
  have h00 : φ (A 0 0) = c := by
    simpa using congrArg (fun X : Matrix (Fin 3) (Fin 3) K => X 0 0) hc
  apply ha
  refine ⟨A 0 0, ?_⟩
  ext i j
  apply φ.injective
  have hij := congrArg (fun X : Matrix (Fin 3) (Fin 3) K => X i j) hc
  by_cases h : i = j <;> simp_all [Matrix.map_apply, Matrix.smul_apply]

private theorem semisimple_of_odd_pow [CharP K 2]
    (A : Matrix (Fin 3) (Fin 3) K) (m : ℕ) (hm : Odd m) (hpow : A ^ m = 1) :
    Module.End.IsSemisimple (Matrix.toLinAlgEquiv' A) := by
  let e : Matrix (Fin 3) (Fin 3) K ≃ₐ[K] Module.End K (Fin 3 → K) := Matrix.toLinAlgEquiv'
  change (e A).IsSemisimple
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C' 2 m (1 : K)
      hm.not_two_dvd_nat one_ne_zero).squarefree
  simp only [map_sub, Polynomial.aeval_X_pow, map_one]
  rw [← map_pow, hpow, map_one, sub_self]

/-- Odd-order nonscalar matrices over any binary field satisfy the same
five-dimensional fixed-space bound; no splitting-field premise remains. -/
theorem matrix_fixed_finrank_le_five_of_odd [CharP K 2]
    (A B : Matrix (Fin 3) (Fin 3) K) (m l : ℕ) (hm : Odd m) (hl : Odd l)
    (hA : A ^ m = 1) (hB : B ^ l = 1)
    (ha : ¬ ∃ c : K, A = c • 1) (hb : ¬ ∃ c : K, B = c • 1)
    {W : Type*} [AddCommGroup W] [Module K W]
    (f : W →ₗ[K] Matrix (Fin 3) (Fin 3) K) (hf : Function.Injective f)
    (hfix : ∀ w, A * f w * B.transpose = f w) : finrank K W ≤ 5 := by
  let C := AlgebraicClosure K
  let φ := algebraMap K C
  let g := (matrixBaseChange C K).toLinearMap.comp (f.baseChange C)
  have hg : Function.Injective g :=
    (matrixBaseChange C K).injective.comp (Module.Flat.lTensor_preserves_injective_linearMap f hf)
  have hgp (a : C) (w : W) : g (a ⊗ₜ[K] w) = a • (f w).map φ := by
    change matrixBaseChange C K (a ⊗ₜ[K] f w) = _
    exact matrixBaseChange_tmul a (f w)
  have hAg : (A.map φ) ^ m = 1 := by
    rw [← Matrix.map_pow, hA]
    exact φ.mapMatrix.map_one
  have hBg : (B.map φ) ^ l = 1 := by
    rw [← Matrix.map_pow, hB]
    exact φ.mapMatrix.map_one
  have hd := matrix_fixed_finrank_le_five (A.map φ) (B.map φ)
    (semisimple_of_odd_pow _ m hm hAg) (semisimple_of_odd_pow _ l hl hBg)
    (matrix_nonscalar_map φ A ha) (matrix_nonscalar_map φ B hb) g hg (by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv => simp only [map_add, Matrix.mul_add, Matrix.add_mul, hu, hv]
      | tmul a w =>
        rw [hgp, Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        change A.map φ * (f w).map φ * (B.transpose.map φ) = (f w).map φ
        rw [← Matrix.map_mul, ← Matrix.map_mul, hfix])
  rwa [Module.finrank_baseChange] at hd

end Representation.TensorThreeFixedSpace
