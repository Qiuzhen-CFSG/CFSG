module

public import Theory.SpecificGroups.Monster.Construction.Symmetric
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Ring

/-!
# The tensor coefficients in the Griess trilinear form

Equation 28.5 gives the natural bilinear form associated with a symmetric
matrix, plus its trace divided by eight. Tensoring with the spin form gives
an actual trilinear `S,W,W` block. Equation 28.6 uses exactly `I - 2t`, where
the source short tensor is `t = ξ ⊗ ξ`; no unit-vector normalization is
inserted. Its tensor coefficient is divided by eight.

An orthogonal involution is self-adjoint, so each short-lift tensor
coefficient is symmetric. A central element acting as minus identity
negates that coefficient, proving the required signed-lift relation when
the natural tensor is unchanged. The spin form, action and short tensor
remain explicit inputs to be supplied by their source constructions.

Source: Aschbacher, *Sporadic Groups*, equations 28.5–28.6 and
Lemmas 28.10–28.11, printed pp. 151–153.
-/

@[expose] public section

noncomputable section
open scoped TensorProduct Matrix
namespace Sporadic.Monster.Construction.Griess

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The natural coefficient in (28.5), with the source trace term. -/
def symmetricNaturalBlock :
    SymmetricPart →ₗ[ℝ] LinearMap.BilinForm ℝ (Fin 24 → ℝ) where
  toFun A := A.val.toBilin' + (Matrix.trace A.val / 8) • Matrix.toBilin' 1
  map_add' A B := by
    simp only [Submodule.coe_add, map_add, Matrix.trace_add, add_div, add_smul]
    abel
  map_smul' r A := by
    simp only [Submodule.coe_smul, map_smul, Matrix.trace_smul, smul_eq_mul,
      RingHom.id_apply, smul_add, smul_smul, mul_div_assoc]

@[simp] theorem symmetricNaturalBlock_apply (A : SymmetricPart) (a b : Fin 24 → ℝ) :
    symmetricNaturalBlock A a b =
      (a ᵥ* A.val) ⬝ᵥ b + Matrix.trace A.val * (a ⬝ᵥ b) / 8 := by
  change A.val.toBilin' a b + (Matrix.trace A.val / 8) * (Matrix.toBilin' 1 a b) = _
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.one_mulVec,
    Matrix.dotProduct_mulVec]
  ring

theorem symmetricNaturalBlock_symmetric (A : SymmetricPart) (a b : Fin 24 → ℝ) :
    symmetricNaturalBlock A a b = symmetricNaturalBlock A b a := by
  have hA := (Matrix.isSymm_toBilin'_iff_isSymm).mpr A.prop
  have hI := (Matrix.isSymm_toBilin'_iff_isSymm).mpr
    (Matrix.isSymm_one (n := Fin 24) (α := ℝ))
  exact (hA.add (hI.smul (Matrix.trace A.val / 8))).eq a b

/-- Tensoring a natural bilinear form with a fixed spin bilinear form is linear. -/
def tensorFormMap (γ : LinearMap.BilinForm ℝ V) :
    LinearMap.BilinForm ℝ (Fin 24 → ℝ) →ₗ[ℝ]
      LinearMap.BilinForm ℝ ((Fin 24 → ℝ) ⊗[ℝ] V) :=
  (LinearMap.BilinForm.tensorDistrib ℝ ℝ).comp ((TensorProduct.mk ℝ _ _).flip γ)

@[simp] theorem tensorFormMap_tmul (γ : LinearMap.BilinForm ℝ V)
    (B : LinearMap.BilinForm ℝ (Fin 24 → ℝ)) (a b : Fin 24 → ℝ) (v w : V) :
    tensorFormMap γ B (a ⊗ₜ[ℝ] v) (b ⊗ₜ[ℝ] w) = B a b * γ v w := by
  change γ v w • B a b = _
  exact mul_comm _ _

theorem tensorFormMap_symmetric (γ : LinearMap.BilinForm ℝ V)
    (B : LinearMap.BilinForm ℝ (Fin 24 → ℝ))
    (hγ : ∀ v w, γ v w = γ w v) (hB : ∀ a b, B a b = B b a)
    (x y : (Fin 24 → ℝ) ⊗[ℝ] V) : tensorFormMap γ B x y = tensorFormMap γ B y x := by
  have h := LinearMap.IsSymm.tmul (B₁ := B) (B₂ := γ)
    (LinearMap.isSymm_def.mpr hB) (LinearMap.isSymm_def.mpr hγ)
  exact h.eq x y

/-- The actual `S,W,W` trilinear block, for an explicitly supplied spin form. -/
def symmetricTensorBlock (γ : LinearMap.BilinForm ℝ V) :
    SymmetricPart →ₗ[ℝ] LinearMap.BilinForm ℝ ((Fin 24 → ℝ) ⊗[ℝ] V) :=
  (tensorFormMap γ).comp symmetricNaturalBlock

@[simp] theorem symmetricTensorBlock_tmul (γ : LinearMap.BilinForm ℝ V)
    (A : SymmetricPart) (a b : Fin 24 → ℝ) (v w : V) :
    symmetricTensorBlock γ A (a ⊗ₜ[ℝ] v) (b ⊗ₜ[ℝ] w) =
      ((a ᵥ* A.val) ⬝ᵥ b + Matrix.trace A.val * (a ⬝ᵥ b) / 8) * γ v w := by
  exact (tensorFormMap_tmul γ (symmetricNaturalBlock A) a b v w).trans
    (congrArg (fun t => t * γ v w) (symmetricNaturalBlock_apply A a b))

theorem symmetricTensorBlock_symmetric (γ : LinearMap.BilinForm ℝ V)
    (hγ : ∀ v w, γ v w = γ w v) (A : SymmetricPart)
    (x y : (Fin 24 → ℝ) ⊗[ℝ] V) :
    symmetricTensorBlock γ A x y = symmetricTensorBlock γ A y x :=
  tensorFormMap_symmetric γ (symmetricNaturalBlock A) hγ
    (symmetricNaturalBlock_symmetric A) x y

/-- The spin matrix coefficient occurring in (28.6). -/
def spinCoefficient (γ : LinearMap.BilinForm ℝ V) (T : Module.End ℝ V) :
    LinearMap.BilinForm ℝ V := LinearMap.comp γ T

theorem involution_self_adjoint (γ : LinearMap.BilinForm ℝ V) (T : Module.End ℝ V)
    (hi : ∀ v, T (T v) = v) (ho : ∀ v w, γ (T v) (T w) = γ v w) (v w : V) :
    γ (T v) w = γ v (T w) := by
  have h := ho v (T w)
  rw [hi] at h
  exact h

theorem spinCoefficient_symmetric (γ : LinearMap.BilinForm ℝ V) (T : Module.End ℝ V)
    (hs : ∀ v w, γ v w = γ w v)
    (hi : ∀ v, T (T v) = v) (ho : ∀ v w, γ (T v) (T w) = γ v w) (v w : V) :
    spinCoefficient γ T v w = spinCoefficient γ T w v :=
  (involution_self_adjoint γ T hi ho v w).trans (hs v (T w))

/-- The natural factor `I - 2t`, where the source supplies `t = ξ ⊗ ξ`.
This is not a normalization of `t` to unit length. -/
def shortNaturalBlock (t : SymmetricPart) : LinearMap.BilinForm ℝ (Fin 24 → ℝ) :=
  Matrix.toBilin' (1 - (2 : ℝ) • t.val)

theorem shortNaturalBlock_symmetric (t : SymmetricPart) (a b : Fin 24 → ℝ) :
    shortNaturalBlock t a b = shortNaturalBlock t b a := by
  apply ((Matrix.isSymm_toBilin'_iff_isSymm).mpr _).eq
  exact Matrix.isSymm_one.sub (t.prop.smul 2)

/-- The exact `(28.6)` bilinear coefficient for a short lift. The source
short tensor and descended spin endomorphism are explicit inputs. -/
def shortTensorBlock (γ : LinearMap.BilinForm ℝ V) (t : SymmetricPart)
    (T : Module.End ℝ V) : LinearMap.BilinForm ℝ ((Fin 24 → ℝ) ⊗[ℝ] V) :=
  (1 / 8 : ℝ) • tensorFormMap (spinCoefficient γ T) (shortNaturalBlock t)

@[simp] theorem shortTensorBlock_tmul (γ : LinearMap.BilinForm ℝ V)
    (t : SymmetricPart) (T : Module.End ℝ V) (a b : Fin 24 → ℝ) (v w : V) :
    shortTensorBlock γ t T (a ⊗ₜ[ℝ] v) (b ⊗ₜ[ℝ] w) =
      shortNaturalBlock t a b * γ (T v) w / 8 := by
  simp only [shortTensorBlock, LinearMap.smul_apply, tensorFormMap_tmul,
    spinCoefficient, LinearMap.comp_apply, smul_eq_mul]
  ring

theorem shortTensorBlock_symmetric (γ : LinearMap.BilinForm ℝ V)
    (t : SymmetricPart) (T : Module.End ℝ V)
    (hs : ∀ v w, γ v w = γ w v)
    (hi : ∀ v, T (T v) = v) (ho : ∀ v w, γ (T v) (T w) = γ v w)
    (x y : (Fin 24 → ℝ) ⊗[ℝ] V) :
    shortTensorBlock γ t T x y = shortTensorBlock γ t T y x := by
  exact congrArg ((1 / 8 : ℝ) • ·)
    (tensorFormMap_symmetric _ _ (spinCoefficient_symmetric γ T hs hi ho)
      (shortNaturalBlock_symmetric t) x y)

/-- Negating the spin action negates the mixed block, while its natural tensor
stays fixed. This is the descent relation for `y(rz) = -y(r)`. -/
theorem shortTensorBlock_neg (γ : LinearMap.BilinForm ℝ V)
    (t : SymmetricPart) (T : Module.End ℝ V) :
    shortTensorBlock γ t (-T) = -shortTensorBlock γ t T := by
  apply TensorProduct.ext'
  intro a v
  apply TensorProduct.ext'
  intro b w
  simp only [LinearMap.neg_apply, shortTensorBlock_tmul, map_neg]
  ring

/-- The natural coefficient after substituting the actual rank-one tensor.
The source short-vector modules supply `ht`; no choice of a lift is made here. -/
theorem shortNaturalBlock_rankOne (t : SymmetricPart) (ξ a b : Fin 24 → ℝ)
    (ht : ∀ i j, t.val i j = ξ i * ξ j) :
    shortNaturalBlock t a b = a ⬝ᵥ b - 2 * (a ⬝ᵥ ξ) * (ξ ⬝ᵥ b) := by
  unfold shortNaturalBlock
  rw [map_sub, map_smul]
  change Matrix.toBilin' 1 a b - 2 * Matrix.toBilin' t.val a b = _
  rw [Matrix.toBilin'_apply', Matrix.one_mulVec, Matrix.toBilin'_apply]
  have ht' : (∑ i, ∑ j, a i * t.val i j * b j) = (a ⬝ᵥ ξ) * (ξ ⬝ᵥ b) := by
    unfold dotProduct
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [ht]
    ring
  rw [ht']
  ring

/-- Formula (28.6) on pure tensors, with its unaltered coefficient. -/
theorem shortTensorBlock_rankOne (γ : LinearMap.BilinForm ℝ V)
    (t : SymmetricPart) (T : Module.End ℝ V) (ξ a b : Fin 24 → ℝ)
    (ht : ∀ i j, t.val i j = ξ i * ξ j) (v w : V) :
    shortTensorBlock γ t T (a ⊗ₜ[ℝ] v) (b ⊗ₜ[ℝ] w) =
      (a ⬝ᵥ b - 2 * (a ⬝ᵥ ξ) * (ξ ⬝ᵥ b)) * γ (T v) w / 8 := by
  rw [shortTensorBlock_tmul, shortNaturalBlock_rankOne t ξ a b ht]

/-- A representation sends a lift differing by the central minus sign to
minus the original spin endomorphism. -/
theorem representation_mul_sign {G : Type*} [Group G]
    (ρ : Representation ℝ G V) (z : G) (hz : ∀ v, ρ z v = -v) (r : G) :
    ρ (r * z) = -ρ r := by
  ext v
  rw [map_mul]
  change ρ r (ρ z v) = -(ρ r v)
  rw [hz, map_neg]

/-- Well-definedness of the short tensor coefficient under the source signed
lift relation, using the two independent sign identities. -/
theorem shortTensorBlock_mul_sign {G : Type*} [Group G]
    (ρ : Representation ℝ G V) (z : G) (hz : ∀ v, ρ z v = -v)
    (γ : LinearMap.BilinForm ℝ V) (t : G → SymmetricPart)
    (ht : ∀ r, t (r * z) = t r) (r : G) :
    shortTensorBlock γ (t (r * z)) (ρ (r * z)) = -shortTensorBlock γ (t r) (ρ r) := by
  rw [ht, representation_mul_sign ρ z hz, shortTensorBlock_neg]

end Sporadic.Monster.Construction.Griess
