module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Plane
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Center

/-!
# Tensor fixed spaces for symplectic involution normal forms

The actual tensor acts on matrices by X ↦ g X σ(g)ᵀ. For an upper shear,
the fixed equations are B S = S σ(B)ᵀ = 0 and B R + Q σ(B)ᵀ = 0.
An invertible B leaves precisely the two free blocks P and Q, hence eight
dimensions. A nonzero rank-one central block leaves ten coordinates.
The displayed linear equivalences identify the spaces, not just their dimensions.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

@[expose] public section
set_option linter.unusedSimpArgs false
open scoped Matrix TensorProduct Classical
open Matrix Representation
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Representation.OneCohomology.SymplecticFour

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F]

noncomputable abbrev matrixFixed (σ : F ≃+* F) (g : Sp F) :=
  LinearMap.ker (matrixAction σ g - LinearMap.id)

lemma mem_matrixFixed (σ : F ≃+* F) (g : Sp F) (X : Mat (F := F)) :
    X ∈ matrixFixed σ g ↔ matrixAction σ g X = X := by
  simp [matrixFixed, LinearMap.mem_ker, sub_eq_zero]

lemma shear_fixed_iff (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    Matrix.fromBlocks P Q R S ∈ matrixFixed σ (Plane.shearSp B) ↔
    B.val * S = 0 ∧ S * (B.val.map σ).transpose = 0 ∧
      B.val * R + Q * (B.val.map σ).transpose = 0 := by
  rw [mem_matrixFixed, shear_blocks]
  constructor
  · intro hh
    have hS := congrArg Matrix.toBlocks₁₂ hh
    have hS' := congrArg Matrix.toBlocks₂₁ hh
    have hP := congrArg Matrix.toBlocks₁₁ hh
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₂₁, add_eq_left] at hS hS' hP
    refine ⟨hS, hS', ?_⟩
    simpa only [hS, add_zero, add_assoc, add_eq_left] using hP
  · rintro ⟨hS,hS',hR⟩
    simp only [hS, hS', add_zero]
    rw [add_assoc, hR, add_zero]

lemma invertible_shear_fixed_iff (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (C : Matrix (Fin 2) (Fin 2) F) (hCB : C * B.val = 1)
    (hBC : B.val * C = 1) (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    Matrix.fromBlocks P Q R S ∈ matrixFixed σ (Plane.shearSp B) ↔
      S = 0 ∧ R = -(C * Q * (B.val.map σ).transpose) := by
  rw [shear_fixed_iff]
  constructor
  · rintro ⟨hS, _, hR⟩
    have hS0 : S = 0 := by
      simpa only [← Matrix.mul_assoc, hCB, Matrix.one_mul, Matrix.mul_zero] using
        congrArg (C * ·) hS
    refine ⟨hS0, ?_⟩
    have he := congrArg (C * ·) hR
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hCB, Matrix.one_mul,
      Matrix.mul_zero] at he
    exact eq_neg_of_add_eq_zero_left he
  · rintro ⟨rfl,rfl⟩
    simp only [Matrix.mul_zero, Matrix.zero_mul, true_and, Matrix.mul_neg,
      ← Matrix.mul_assoc, hBC, Matrix.one_mul, neg_add_cancel]

noncomputable def invertibleShearFixedEquiv (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (C : Matrix (Fin 2) (Fin 2) F) (hCB : C * B.val = 1) (hBC : B.val * C = 1) :
    matrixFixed σ (Plane.shearSp B) ≃ₗ[F]
      (Matrix (Fin 2) (Fin 2) F × Matrix (Fin 2) (Fin 2) F) where
  toFun X := (X.val.toBlocks₁₁, X.val.toBlocks₁₂)
  invFun PQ := ⟨Matrix.fromBlocks PQ.1 PQ.2 (-(C * PQ.2 * (B.val.map σ).transpose)) 0,
    (invertible_shear_fixed_iff σ B C hCB hBC _ _ _ _).mpr ⟨rfl,rfl⟩⟩
  left_inv X := by
    apply Subtype.ext
    have hh := X.property
    rw [← Matrix.fromBlocks_toBlocks X.val, invertible_shear_fixed_iff σ B C hCB hBC] at hh
    simpa only [hh.1,hh.2] using Matrix.fromBlocks_toBlocks X.val
  right_inv PQ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma invertible_shear_fixed_finrank (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (C : Matrix (Fin 2) (Fin 2) F) (hCB : C * B.val = 1) (hBC : B.val * C = 1) :
    Module.finrank F (matrixFixed σ (Plane.shearSp B)) = 8 := by
  rw [(invertibleShearFixedEquiv σ B C hCB hBC).finrank_eq]
  norm_num [Module.finrank_prod, Module.finrank_matrix]
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F]
noncomputable def centralBlock (a b : F) : Plane.symmetricMatrices F :=
  ⟨!![a,b;b,0], by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩

lemma rankOne_fixed_iff (σ : F ≃+* F) {a : F} (ha : a ≠ 0)
    (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    Matrix.fromBlocks P Q R S ∈ matrixFixed σ (Plane.shearSp (centralBlock a 0)) ↔
      S 0 0 = 0 ∧ S 0 1 = 0 ∧ S 1 0 = 0 ∧ R 0 1 = 0 ∧ Q 1 0 = 0 ∧
        R 0 0 = -(σ a / a * Q 0 0) := by
  have hσa : σ a ≠ 0 := (map_ne_zero σ).mpr ha
  rw [shear_fixed_iff]
  change (!![a,0;0,0] * S = 0 ∧ S * (!![a,0;0,0].map σ).transpose = 0 ∧
    !![a,0;0,0] * R + Q * (!![a,0;0,0].map σ).transpose = 0) ↔ _
  simp only [← Matrix.ext_iff, Fin.forall_fin_two, Matrix.mul_apply,
    Matrix.add_apply, Matrix.zero_apply, Matrix.transpose_apply, Matrix.map_apply,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.of_apply, zero_mul, mul_zero, add_zero, zero_add, map_zero]
  constructor
  · rintro ⟨⟨⟨h00,h01⟩,_⟩,⟨_,h10,_⟩,⟨⟨hR,hR01⟩,hQ10,_⟩⟩
    refine ⟨(mul_eq_zero.mp h00).resolve_left ha,
      (mul_eq_zero.mp h01).resolve_left ha,
      (mul_eq_zero.mp h10).resolve_right hσa,
      (mul_eq_zero.mp hR01).resolve_left ha,
      (mul_eq_zero.mp hQ10).resolve_right hσa, ?_⟩
    apply (mul_left_cancel₀ ha)
    rw [mul_neg]
    have hh : a * (σ a / a * Q 0 0) = Q 0 0 * σ a := by field_simp
    rw [hh]
    exact eq_neg_of_add_eq_zero_left hR
  · rintro ⟨h00,h01,h10,hR01,hQ10,hR⟩
    simp only [h00,h01,h10,hR01,hQ10,hR,mul_zero,zero_mul,add_zero,and_self]
    field_simp
    simp

noncomputable def rankOneFixedEquiv (σ : F ≃+* F) {a : F} (ha : a ≠ 0) :
    matrixFixed σ (Plane.shearSp (centralBlock a 0)) ≃ₗ[F]
      (Matrix (Fin 2) (Fin 2) F × (Fin 6 → F)) where
  toFun X := (X.val.toBlocks₁₁, ![X.val (.inl 0) (.inr 0),
    X.val (.inl 0) (.inr 1), X.val (.inl 1) (.inr 1),
    X.val (.inr 1) (.inl 0), X.val (.inr 1) (.inl 1), X.val (.inr 1) (.inr 1)])
  invFun PQ := ⟨Matrix.fromBlocks PQ.1 !![PQ.2 0,PQ.2 1;0,PQ.2 2]
    !![-(σ a / a * PQ.2 0),0;PQ.2 3,PQ.2 4] !![0,0;0,PQ.2 5],
    (rankOne_fixed_iff σ ha _ _ _ _).mpr (by simp)⟩
  left_inv X := by
    apply Subtype.ext
    have hh := X.property
    rw [← Matrix.fromBlocks_toBlocks X.val, rankOne_fixed_iff σ ha] at hh
    rcases hh with ⟨h00,h01,h10,hR,hQ,hQR⟩
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j
    all_goals simp_all [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
  right_inv PQ := by
    rcases PQ with ⟨P,Q⟩
    refine Prod.ext ?_ ?_
    · rfl
    · ext i
      fin_cases i <;> rfl
  map_add' X Y := by
    refine Prod.ext ?_ ?_
    · rfl
    · ext i; fin_cases i <;> rfl
  map_smul' c X := by
    refine Prod.ext ?_ ?_
    · rfl
    · ext i; fin_cases i <;> rfl

lemma rankOne_fixed_finrank (σ : F ≃+* F) {a : F} (ha : a ≠ 0) :
    Module.finrank F (matrixFixed σ (Plane.shearSp (centralBlock a 0))) = 10 := by
  rw [(rankOneFixedEquiv σ ha).finrank_eq]
  norm_num [Module.finrank_prod, Module.finrank_matrix, Module.finrank_pi_fintype]
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F]

lemma mem_cyclicInvariants {D U : Type*} [Group D] [AddCommGroup U] [Module F U]
    (ρ : Representation F D U) (g : D) (v : U) :
    v ∈ invariants (ρ.comp (Subgroup.zpowers g).subtype) ↔ ρ g v = v := by
  apply Representation.mem_invariants_iff_of_forall_mem_zpowers
    (ρ.comp (Subgroup.zpowers g).subtype) ⟨g, Subgroup.mem_zpowers g⟩
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

noncomputable def cyclicInvariantsCoordinates (σ : F ≃+* F) (g : Sp F) :
    invariants ((twistedTensor σ).comp (Subgroup.zpowers g).subtype) ≃ₗ[F]
      matrixFixed σ g where
  toFun x := ⟨coordinates x.val, by
    rw [mem_matrixFixed, ← coordinates_action]
    exact congrArg coordinates ((mem_cyclicInvariants _ _ _).mp x.property)⟩
  invFun X := ⟨coordinates.symm X.val, by
    rw [mem_cyclicInvariants]
    apply coordinates.injective
    rw [coordinates_action, LinearEquiv.apply_symm_apply]
    exact (mem_matrixFixed _ _ _).mp X.property⟩
  left_inv x := Subtype.ext (coordinates.symm_apply_apply x.val)
  right_inv X := Subtype.ext (coordinates.apply_symm_apply X.val)
  map_add' x y := Subtype.ext (map_add coordinates x.val y.val)
  map_smul' c x := Subtype.ext (map_smul coordinates c x.val)

noncomputable def cyclicInvariantsConj {D U : Type*} [Group D] [AddCommGroup U] [Module F U]
    (ρ : Representation F D U) (g c : D) :
    invariants (ρ.comp (Subgroup.zpowers g).subtype) ≃ₗ[F]
      invariants (ρ.comp (Subgroup.zpowers (c*g*c⁻¹)).subtype) where
  toFun x := ⟨ρ c x.val, by
    rw [mem_cyclicInvariants]
    have hx := (mem_cyclicInvariants _ _ _).mp x.property
    simp only [map_mul, map_inv, Module.End.mul_apply]
    simpa using congrArg (ρ c) hx⟩
  invFun x := ⟨ρ c⁻¹ x.val, by
    rw [mem_cyclicInvariants]
    have hx := (mem_cyclicInvariants _ _ _).mp x.property
    have he := congrArg (ρ c⁻¹) hx
    simp only [map_mul, Module.End.mul_apply] at he
    simpa using he⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp
  map_add' x y := Subtype.ext (map_add (ρ c) x.val y.val)
  map_smul' a x := Subtype.ext (map_smul (ρ c) a x.val)

variable [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
lemma central_eq_shear (a b : F) :
    rootElement 0 a * rootElement 4 b = Plane.shearSp (centralBlock a b) := by
  apply Subtype.ext
  exact central_matrix a b

lemma central_fixed_finrank_of_right_ne_zero (σ : F ≃+* F) (a : F) {b : F} (hb : b ≠ 0) :
    Module.finrank F (invariants ((twistedTensor σ).comp
      (Subgroup.zpowers (rootElement 0 a * rootElement 4 b)).subtype)) = 8 := by
  rw [(cyclicInvariantsCoordinates σ _).finrank_eq, central_eq_shear]
  let C : Matrix (Fin 2) (Fin 2) F := !![0,b⁻¹;b⁻¹,-(a/b^2)]
  apply invertible_shear_fixed_finrank σ _ C
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, centralBlock, Matrix.mul_apply, Fin.sum_univ_two, hb]
    all_goals field_simp
    all_goals ring

lemma central_fixed_finrank_of_right_zero (σ : F ≃+* F) {a : F} (ha : a ≠ 0) :
    Module.finrank F (invariants ((twistedTensor σ).comp
      (Subgroup.zpowers (rootElement 0 a * rootElement 4 0)).subtype)) = 10 := by
  rw [(cyclicInvariantsCoordinates σ _).finrank_eq, central_eq_shear]
  exact rankOne_fixed_finrank σ ha
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

