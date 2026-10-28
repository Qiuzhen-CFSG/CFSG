module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Natural
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The plane radical on the coefficient-twisted symplectic tensor

The coordinate map sends x tensor y to the outer-product matrix, so the
actual tensor action is X ↦ g X σ(g)ᵀ. Scalar upper shears force the bottom
block of an invariant matrix to vanish; a scalar moved by σ then forces both
off-diagonal blocks to vanish. Thus the fixed space is precisely the tensor
square of the natural isotropic plane, of defining-field dimension four.

Each natural displacement lands in the fixed plane. Distributing tensor
displacements shows that three successive displacements vanish.
Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457.
-/

@[expose] public section
open scoped TensorProduct Matrix
open Matrix Representation
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F]
abbrev Mat := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

noncomputable def coordinates : (Vector F ⊗[F] Vector F) ≃ₗ[F] Mat (F := F) :=
  (TensorProduct.comm F (Vector F) (Vector F)).trans
    (TensorProduct.piScalarRight F F (Vector F) (Fin 2 ⊕ Fin 2))

lemma coordinates_tmul (x y : Vector F) :
    coordinates (x ⊗ₜ[F] y) = Matrix.vecMulVec x y := by
  ext i j
  change (TensorProduct.piScalarRight F F (Vector F) (Fin 2 ⊕ Fin 2))
    (y ⊗ₜ[F] x) i j = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

noncomputable def matrixAction (σ : F ≃+* F) : Representation F (Sp F) (Mat (F := F)) where
  toFun g := {
    toFun X := g.val * X * (g.val.map σ).transpose
    map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by intros; simp }
  map_one' := by ext X i j; simp
  map_mul' g h := by
    ext X i j
    change ((g * h).val * X * (((g * h).val).map σ).transpose) i j =
      (g.val * (h.val * X * (h.val.map σ).transpose) * (g.val.map σ).transpose) i j
    change ((g.val * h.val) * X * ((g.val * h.val).map σ).transpose) i j = _
    rw [Matrix.map_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

lemma coordinates_action (σ : F ≃+* F) (g : Sp F) (u : Vector F ⊗[F] Vector F) :
    coordinates (CFSG.Quasithin.ChapterK.Symplectic.twistedTensor σ g u) =
      matrixAction σ g (coordinates u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | tmul x y =>
    change coordinates (symplecticNatural 2 g x ⊗ₜ[F]
      symplecticNatural 2 (DiagramAutomorphisms.fieldAutomorphism σ g) y) = _
    rw [coordinates_tmul, coordinates_tmul]
    change Matrix.vecMulVec (g.val.mulVec x)
      ((g.val.map σ).mulVec y) = _
    change _ = g.val * Matrix.vecMulVec x y * (g.val.map σ).transpose
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

lemma shear_blocks (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    matrixAction σ (Plane.shearSp B) (Matrix.fromBlocks P Q R S) =
      Matrix.fromBlocks (P + B.val * R + (Q + B.val * S) * (B.val.map σ).transpose)
        (Q + B.val * S) (R + S * (B.val.map σ).transpose) S := by
  change Matrix.fromBlocks 1 B.val 0 1 * Matrix.fromBlocks P Q R S *
    ((Matrix.fromBlocks 1 B.val 0 1).map σ).transpose = _
  simp [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

noncomputable def scalarShear (t : F) : Plane.symmetricMatrices F :=
  ⟨t • (1 : Matrix (Fin 2) (Fin 2) F), by
    change (t • (1 : Matrix (Fin 2) (Fin 2) F)).transpose = _
    simp⟩

lemma scalarShear_blocks (σ : F ≃+* F) (t : F)
    (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    matrixAction σ (Plane.shearSp (scalarShear t)) (Matrix.fromBlocks P Q R S) =
      Matrix.fromBlocks (P + t • R + σ t • (Q + t • S))
        (Q + t • S) (R + σ t • S) S := by
  rw [shear_blocks]
  have hs : ((scalarShear t).val.map σ).transpose = σ t • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    by_cases hij : i = j <;> simp [scalarShear, hij, eq_comm]
  rw [hs]
  simp [scalarShear]

lemma blocks_fixed_iff (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    (∀ g : planeRadical (F := F), matrixAction σ g.val (Matrix.fromBlocks P Q R S) =
      Matrix.fromBlocks P Q R S) ↔ Q = 0 ∧ R = 0 ∧ S = 0 := by
  constructor
  · intro h
    have ht (t : F) := h ⟨Plane.shearSp (scalarShear t),
      (mem_planeRadical_iff _).mpr ⟨scalarShear t, rfl⟩⟩
    simp only [scalarShear_blocks] at ht
    have hS : S = 0 := by
      have hh := congrArg Matrix.toBlocks₁₂ (ht 1)
      simpa using hh
    have hQR : R + Q = 0 := by
      have hh := congrArg Matrix.toBlocks₁₁ (ht 1)
      simpa [hS, add_assoc] using hh
    have hex : ∃ t, σ t ≠ t := by
      by_contra! he
      apply hne
      ext t
      exact he t
    obtain ⟨t, htne⟩ := hex
    have he : t • R + σ t • Q = 0 := by
      have hh := congrArg Matrix.toBlocks₁₁ (ht t)
      simpa [hS, add_assoc] using hh
    have hQ : Q = 0 := by
      have hR : R = -Q := eq_neg_of_add_eq_zero_left hQR
      rw [hR] at he
      have hh : (σ t - t) • Q = 0 := by
        rw [sub_smul]
        simpa [smul_neg, sub_eq_add_neg, add_comm] using he
      exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr htne)
    exact ⟨hQ, by simpa [hQ] using hQR, hS⟩
  · rintro ⟨rfl, rfl, rfl⟩ g
    obtain ⟨B, hB⟩ := (mem_planeRadical_iff g.val).mp g.property
    rw [← hB, shear_blocks]
    simp
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F]

noncomputable def matrixPlaneInvariantsEquiv (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F) :
    (Representation.invariants ((matrixAction σ).comp (planeRadical (F := F)).subtype)) ≃ₗ[F]
      Matrix (Fin 2) (Fin 2) F where
  toFun X := X.val.toBlocks₁₁
  invFun P := ⟨Matrix.fromBlocks P 0 0 0,
    (blocks_fixed_iff σ hne P 0 0 0).mpr ⟨rfl, rfl, rfl⟩⟩
  left_inv X := by
    apply Subtype.ext
    have hh : ∀ g : planeRadical (F := F),
        matrixAction σ g.val (Matrix.fromBlocks X.val.toBlocks₁₁ X.val.toBlocks₁₂
          X.val.toBlocks₂₁ X.val.toBlocks₂₂) =
        Matrix.fromBlocks X.val.toBlocks₁₁ X.val.toBlocks₁₂ X.val.toBlocks₂₁ X.val.toBlocks₂₂ := by
      intro g
      simpa only [Matrix.fromBlocks_toBlocks, MonoidHom.comp_apply, Subgroup.coe_subtype] using X.property g
    obtain ⟨hQ, hR, hS⟩ := (blocks_fixed_iff σ hne _ _ _ _).mp hh
    simpa only [hQ, hR, hS] using (Matrix.fromBlocks_toBlocks X.val)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def planeInvariantsCoordinates (σ : F ≃+* F) :
    (Representation.invariants ((CFSG.Quasithin.ChapterK.Symplectic.twistedTensor σ).comp
      (planeRadical (F := F)).subtype)) ≃ₗ[F]
    (Representation.invariants ((matrixAction σ).comp (planeRadical (F := F)).subtype)) where
  toFun x := ⟨coordinates x.val, by
    intro g
    change matrixAction σ g.val (coordinates x.val) = coordinates x.val
    rw [← coordinates_action]
    exact congrArg coordinates (x.property g)⟩
  invFun X := ⟨coordinates.symm X.val, by
    intro g
    apply coordinates.injective
    change coordinates (CFSG.Quasithin.ChapterK.Symplectic.twistedTensor σ g.val
      (coordinates.symm X.val)) = _
    rw [coordinates_action, LinearEquiv.apply_symm_apply]
    exact X.property g⟩
  left_inv x := Subtype.ext (coordinates.symm_apply_apply x.val)
  right_inv X := Subtype.ext (coordinates.apply_symm_apply X.val)
  map_add' x y := Subtype.ext (map_add coordinates x.val y.val)
  map_smul' c x := Subtype.ext (map_smul coordinates c x.val)

theorem plane_tensor_fixed_finrank (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F) :
    Module.finrank F ((Representation.invariants ((CFSG.Quasithin.ChapterK.Symplectic.twistedTensor σ).comp
      (planeRadical (F := F)).subtype))) = 4 := by
  rw [(planeInvariantsCoordinates σ).finrank_eq,
    (matrixPlaneInvariantsEquiv σ hne).finrank_eq]
  norm_num [Module.finrank_matrix]
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
open scoped TensorProduct
open Representation

section
variable {F D U W : Type*} [Field F] [Group D]
  [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]

private theorem tensor_cubic_of_quadratic (ρ : Representation F D U) (τ : Representation F D W) (A : Subgroup D)
    (hρ : ∀ a ∈ A, ∀ b ∈ A, ∀ x, ρ a (ρ b x - x) = ρ b x - x)
    (hτ : ∀ a ∈ A, ∀ b ∈ A, ∀ y, τ a (τ b y - y) = τ b y - y)
    (a : D) (ha : a ∈ A) (b : D) (hb : b ∈ A) (c : D) (hc : c ∈ A)
    (z : U ⊗[F] W) :
    ((ρ.tprod τ) a - (LinearMap.id : Module.End F (U ⊗[F] W)))
      (((ρ.tprod τ) b - (LinearMap.id : Module.End F (U ⊗[F] W))) (((ρ.tprod τ) c - (LinearMap.id : Module.End F (U ⊗[F] W))) z)) = 0 := by
  let d (g : D) : Module.End F (U ⊗[F] W) := (ρ.tprod τ) g - LinearMap.id
  change d a (d b (d c z)) = 0
  have ht (g : D) (x : U) (y : W) :
      d g (x ⊗ₜ[F] y) = (ρ g x - x) ⊗ₜ[F] τ g y + x ⊗ₜ[F] (τ g y - y) := by
    simp only [d, LinearMap.sub_apply, LinearMap.id_apply, Representation.tprod_apply,
      TensorProduct.map_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  have hl (g : D) (x : U) (y : W) (hx : ρ g x = x) :
      d g (x ⊗ₜ[F] y) = x ⊗ₜ[F] (τ g y - y) := by
    rw [ht, hx, sub_self, TensorProduct.zero_tmul, zero_add]
  have hr (g : D) (x : U) (y : W) (hy : τ g y = y) :
      d g (x ⊗ₜ[F] y) = (ρ g x - x) ⊗ₜ[F] y := by
    rw [ht, hy, sub_self, TensorProduct.tmul_zero, add_zero]
  have hz (g : D) (x : U) (y : W) (hx : ρ g x = x) (hy : τ g y = y) :
      d g (x ⊗ₜ[F] y) = 0 := by
    rw [hl g x y hx, hy, sub_self, TensorProduct.tmul_zero]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul x y =>
    rw [ht, map_add, hl b _ _ (hρ b hb c hc x), hr b _ _ (hτ b hb c hc y), map_add,
      hz a _ _ (hρ a ha c hc x) (hτ a ha b hb (τ c y)),
      hz a _ _ (hρ a ha b hb x) (hτ a ha c hc y), add_zero]
end

open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
theorem field_mem_planeRadical {F : Type*} [Field F] (σ : F ≃+* F) {g : Sp F}
    (hg : g ∈ planeRadical) : DiagramAutomorphisms.fieldAutomorphism σ g ∈ planeRadical := by
  obtain ⟨B, rfl⟩ := (mem_planeRadical_iff g).mp hg
  apply (mem_planeRadical_iff _).mpr
  refine ⟨⟨B.val.map σ, ?_⟩, ?_⟩
  · change (B.val.map σ).transpose = B.val.map σ
    rw [← Matrix.transpose_map, B.property]
  · apply Subtype.ext
    ext i j
    change (Matrix.fromBlocks 1 (B.val.map σ) 0 1) i j =
      σ ((Matrix.fromBlocks 1 B.val 0 1) i j)
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

open CFSG.Quasithin.ChapterK.Symplectic
open Representation.BinaryOffender

theorem plane_tensor_cubic {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] (σ : F ≃+* F)
    (a : Sp F) (ha : a ∈ planeRadical) (b : Sp F) (hb : b ∈ planeRadical)
    (c : Sp F) (hc : c ∈ planeRadical) (z : Vector F ⊗[F] Vector F) :
    (twistedTensor σ a - (LinearMap.id : Module.End F (Vector F ⊗[F] Vector F)))
      ((twistedTensor σ b - (LinearMap.id : Module.End F (Vector F ⊗[F] Vector F)))
      ((twistedTensor σ c - (LinearMap.id : Module.End F (Vector F ⊗[F] Vector F))) z)) = 0 := by
  apply tensor_cubic_of_quadratic _ _ planeRadical ?_ ?_ a ha b hb c hc z
  · exact Natural.planeRadical_quadratic
  · intro a ha b hb y
    exact Natural.planeRadical_quadratic _ (field_mem_planeRadical σ ha)
      _ (field_mem_planeRadical σ hb) y


end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
open CFSG.Quasithin.ChapterK.Symplectic
open Representation.BinaryOffender
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

noncomputable def planeTensorSpace : Submodule F (Vector F ⊗[F] Vector F) :=
  LinearMap.range (TensorProduct.map (plane F).subtype (plane F).subtype)

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem planeTensorSpace_finrank : Module.finrank F (planeTensorSpace (F := F)) = 4 := by
  rw [planeTensorSpace, LinearMap.finrank_range_of_inj
    (TensorProduct.map_injective_of_flat_flat _ _ (plane F).subtype_injective
      (plane F).subtype_injective), Module.finrank_tensorProduct, finrank_plane]

theorem plane_tensor_invariants (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F) :
    Representation.invariants ((twistedTensor σ).comp (planeRadical (F := F)).subtype) =
      planeTensorSpace := by
  have hle : planeTensorSpace (F := F) ≤
      Representation.invariants ((twistedTensor σ).comp (planeRadical (F := F)).subtype) := by
    rintro _ ⟨z, rfl⟩
    intro g
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [TensorProduct.map_tmul]
      change symplecticNatural 2 g.val x.val ⊗ₜ[F]
        symplecticNatural 2 (DiagramAutomorphisms.fieldAutomorphism σ g.val) y.val =
          x.val ⊗ₜ[F] y.val
      have hx : x.val ∈ fixedSpace (binaryNatural (F := F)) planeRadical := by
        rw [planeRadical_natural_fixedSpace]
        exact x.property
      have hy : y.val ∈ fixedSpace (binaryNatural (F := F)) planeRadical := by
        rw [planeRadical_natural_fixedSpace]
        exact y.property
      have hx' : symplecticNatural 2 g.val x.val = x.val := hx g
      have hy' : symplecticNatural 2 (DiagramAutomorphisms.fieldAutomorphism σ g.val) y.val =
          y.val := hy ⟨_, field_mem_planeRadical σ g.property⟩
      rw [hx', hy']
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [planeTensorSpace_finrank, plane_tensor_fixed_finrank σ hne]
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
