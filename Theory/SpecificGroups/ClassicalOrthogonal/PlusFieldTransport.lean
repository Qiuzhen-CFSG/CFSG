module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison.Transport

/-!
# Field transport of the actual split orthogonal carriers

Coefficient transport is a semilinear isometry of the hyperbolic quadratic
forms. It carries each literal Siegel generator to the generator with
transported parameters, hence identifies their generated elementary groups.
The faithful characteristic-two projective maps give the projective group
equivalence. This supplies the field transport needed by the A.2 source
parabolic and binary D3/D4 consumers without replacing the elementary group
by the full orthogonal commutator.
Source: GLS3 §2.7; Aschbacher--Smith A.2.18, printed p.40.
-/

public noncomputable section
open Theory.AlgebraicGroup Subgroup
namespace ClassicalOrthogonal.PlusFieldTransport
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

def coefficientEquiv (σ : F ≃+* K) (r : ℕ) :
    VectorD r F ≃ₛₗ[(σ : F →+* K)] VectorD r K where
  toFun x i := σ (x i)
  invFun x i := σ.symm (x i)
  left_inv x := by ext i; exact σ.symm_apply_apply _
  right_inv x := by ext i; exact σ.apply_symm_apply _
  map_add' x y := by ext i; exact map_add σ _ _
  map_smul' a x := by ext i; exact map_mul σ _ _

@[simp] theorem form_coefficientEquiv (σ : F ≃+* K) (r : ℕ) (x : VectorD r F) :
    formD r K (coefficientEquiv σ r x) = σ (formD r F x) := by
  simp [formD_apply, coefficientEquiv, map_sum]

@[simp] theorem polar_coefficientEquiv (σ : F ≃+* K) (r : ℕ) (x y : VectorD r F) :
    (formD r K).polarBilin (coefficientEquiv σ r x) (coefficientEquiv σ r y) =
      σ ((formD r F).polarBilin x y) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ← map_add, form_coefficientEquiv, map_sub]

def orthogonalEquiv (σ : F ≃+* K) (r : ℕ) :
    quadraticIsometrySubgroup (formD r F) ≃* quadraticIsometrySubgroup (formD r K) :=
  TheoremDRootNormalizer.MinusTwoComparison.orthogonalSemilinearCongr
    σ (coefficientEquiv σ r) (form_coefficientEquiv σ r)

/-- Field transport intertwines the actual natural actions. -/
@[simp] theorem orthogonalEquiv_apply (σ : F ≃+* K) (r : ℕ)
    (g : quadraticIsometrySubgroup (formD r F)) (x : VectorD r F) :
    (orthogonalEquiv σ r g).val (coefficientEquiv σ r x) =
      coefficientEquiv σ r (g.val x) :=
  TheoremDRootNormalizer.MinusTwoComparison.orthogonalSemilinearCongr_apply
    σ (coefficientEquiv σ r) (form_coefficientEquiv σ r) g x

theorem orthogonalEquiv_siegel (σ : F ≃+* K) (r : ℕ) (x y : VectorD r F)
    (hx : formD r F x = 0) (hxy : (formD r F).polarBilin x y = 0) :
    orthogonalEquiv σ r (siegelElement (formD r F) x y hx hxy) =
      siegelElement (formD r K) (coefficientEquiv σ r x) (coefficientEquiv σ r y)
        (by rw [form_coefficientEquiv, hx, map_zero])
        (by rw [polar_coefficientEquiv, hxy, map_zero]) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  obtain ⟨z, rfl⟩ := (coefficientEquiv σ r).surjective z
  rw [orthogonalEquiv_apply]
  change coefficientEquiv σ r (Quadratic.siegel (formD r F) x y z) =
    Quadratic.siegel (formD r K) (coefficientEquiv σ r x)
      (coefficientEquiv σ r y) (coefficientEquiv σ r z)
  simp only [Quadratic.siegel, map_add, map_sub, map_smulₛₗ,
    RingHom.coe_coe, form_coefficientEquiv, polar_coefficientEquiv, map_mul]

theorem orthogonalEquiv_mem_elementary (σ : F ≃+* K) (r : ℕ)
    (g : quadraticIsometrySubgroup (formD r F)) (hg : g ∈ elementarySubgroup (formD r F)) :
    orthogonalEquiv σ r g ∈ elementarySubgroup (formD r K) := by
  have hle : elementarySubgroup (formD r F) ≤
      (elementarySubgroup (formD r K)).comap (orthogonalEquiv σ r).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro k ⟨x,y,hx,hxy,rfl⟩
    change orthogonalEquiv σ r (siegelElement (formD r F) x y hx hxy) ∈ elementarySubgroup (formD r K)
    rw [orthogonalEquiv_siegel]
    exact siegelElement_mem _ _ _ _ _
  exact hle hg

theorem orthogonalEquiv_apply_symm (σ : F ≃+* K) (r : ℕ)
    (g : quadraticIsometrySubgroup (formD r K)) :
    orthogonalEquiv σ r (orthogonalEquiv σ.symm r g) = g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx (z : VectorD r K) : coefficientEquiv σ r (coefficientEquiv σ.symm r z) = z := by
    ext i
    exact σ.apply_symm_apply _
  conv_lhs => rw [← hx x]
  rw [orthogonalEquiv_apply, orthogonalEquiv_apply, hx]

theorem map_elementary (σ : F ≃+* K) (r : ℕ) :
    (elementarySubgroup (formD r F)).map (orthogonalEquiv σ r).toMonoidHom =
      elementarySubgroup (formD r K) := by
  apply le_antisymm
  · rintro g ⟨x,hx,rfl⟩
    exact orthogonalEquiv_mem_elementary σ r x hx
  · intro g hg
    exact ⟨orthogonalEquiv σ.symm r g,
      orthogonalEquiv_mem_elementary σ.symm r g hg, orthogonalEquiv_apply_symm σ r g⟩

def elementaryEquiv (σ : F ≃+* K) (r : ℕ) : OmegaPlus r F ≃* OmegaPlus r K :=
  ((orthogonalEquiv σ r).subgroupMap _).trans (MulEquiv.subgroupCongr (map_elementary σ r))

def projectiveEquiv [CharP F 2] [CharP K 2] (σ : F ≃+* K) (r : ℕ) :
    POmegaPlus r F ≃* POmegaPlus r K :=
  (TheoremDRootNormalizer.elementaryProjectiveEquiv (formD r F)).symm.trans
    ((elementaryEquiv σ r).trans (TheoremDRootNormalizer.elementaryProjectiveEquiv (formD r K)))
end ClassicalOrthogonal.PlusFieldTransport
