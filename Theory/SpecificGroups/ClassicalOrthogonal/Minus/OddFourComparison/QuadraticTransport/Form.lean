module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison.Transport
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The norm coordinates of the chosen anisotropic plane

Transport the original parameter to the actual fixed field. Its polynomial
`X² + X - a` is irreducible, and its degree-two root field embeds into the
finite quadratic extension. The two roots are `α` and `-1-α`, so the norm
of `x-yα` is exactly `x²+xy-ay²`. Anisotropy and equal dimensions give the
plane equivalence. Negating the second hyperbolic coordinate gives an
isometry with the published negative-determinant form, with no change of
quadratic values.

This extends the argument of `OrthogonalFourMinusHermitianEquiv.FormIsometry`
without its characteristic-two identities. The coefficient transport and
full-isometry conjugation APIs come from `MinusTwoComparison.Transport`;
its characteristic-two scalar simplification is not used.
Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport
open Polynomial
open ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u
variable {E : Type u} [Field E]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "K" => HermitianModel.fixedField σ

private theorem exists_parameter_root [Finite E] (hdim : Module.finrank K E = 2)
    (a : K) (ha : ∀ x : K, x ^ 2 + x ≠ a) :
    ∃ α : E, α ^ 2 + α = (a : E) := by
  let p : K[X] := X ^ 2 + X - C a
  have hd : p.natDegree = 2 := by
    dsimp [p]
    rw [natDegree_sub_C, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp
  have hi : Irreducible p := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · simp [hd]
    · intro x hx
      apply ha x
      simpa [p, IsRoot, sub_eq_zero] using hx
  let : Fact (Irreducible p) := ⟨hi⟩
  have he : Nonempty (AdjoinRoot p →ₐ[K] E) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      rw [(AdjoinRoot.powerBasis hi.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hd, hdim])
  let e := he.some
  refine ⟨e (AdjoinRoot.root p), ?_⟩
  have h := AdjoinRoot.aeval_algHom_eq_zero p e
  simp only [p, map_sub, map_add, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

variable (a : HermitianModel.fixedField σ)
  (ha : ∀ x : HermitianModel.fixedField σ, x ^ 2 + x ≠ a) (α : E)
  (hα : α ^ 2 + α = (a : E))

private theorem conjugation_coe (x : K) : σ (x : E) = x := x.property

include ha hα in
private theorem root_not_fixed : σ α ≠ α := by
  intro h
  let x : K := ⟨α, h⟩
  apply ha x
  exact Subtype.ext hα

include ha hα in
private theorem conjugation_root : σ α = -1 - α := by
  have hc := congrArg σ hα
  simp only [map_add, map_pow, conjugation_coe] at hc
  have hmul : (σ α - α) * (σ α + α + 1) = 0 := by
    linear_combination hc - hα
  have hsum := (mul_eq_zero.mp hmul).resolve_left
    (sub_ne_zero.mpr (root_not_fixed σ a ha α hα))
  linear_combination hsum

private def planeToField : (K × K) →ₗ[K] E where
  toFun v := v.1.val - v.2.val * α
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Subfield.coe_add]
    ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Subfield.coe_mul,
      Subfield.smul_def, RingHom.id_apply]
    ring

include ha hα in
private theorem norm_planeToField (v : K × K) :
    HermitianModel.norm σ hσ (planeToField σ α v) = plane K a v := by
  apply Subtype.ext
  simp only [HermitianModel.norm, planeToField, LinearMap.coe_mk, AddHom.coe_mk,
    plane_apply, Subfield.coe_sub, Subfield.coe_add, SubmonoidClass.coe_pow,
    Subfield.coe_mul, map_sub, map_mul, conjugation_coe,
    conjugation_root σ a ha α hα]
  linear_combination -v.2.val ^ 2 * hα

include hσ ha hα in
private theorem planeToField_injective : Function.Injective (planeToField σ α) := by
  intro v w h
  apply sub_eq_zero.mp
  apply plane_anisotropic K a ha
  rw [← norm_planeToField σ hσ a ha α hα, map_sub, h, sub_self]
  exact (HermitianModel.norm_eq_zero_iff σ hσ 0).mpr rfl

variable [Finite E]

private def planeFieldEquiv (hdim : Module.finrank K E = 2) : (K × K) ≃ₗ[K] E :=
  (planeToField σ α).linearEquivOfInjective
    (planeToField_injective σ hσ a ha α hα) (by
      rw [Module.finrank_prod, hdim]
      simp)

private def hyperbolicSign : (K × K) ≃ₗ[K] (K × K) where
  toFun v := (v.1, -v.2)
  invFun v := (v.1, -v.2)
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by simp [add_comm]
  map_smul' c v := by simp

private def formHermitianIsometry (hdim : Module.finrank K E = 2) :
    (form K 1 a).IsometryEquiv (HermitianModel.minusForm σ hσ) where
  toLinearEquiv :=
    (((LinearEquiv.funUnique (Fin 1) K (K × K)).trans (hyperbolicSign σ)).prodCongr
      (planeFieldEquiv σ hσ a ha α hα hdim)).trans (HermitianModel.coordinates σ hσ).symm
  map_app' v := by
    change HermitianModel.minusForm σ hσ
      ((HermitianModel.coordinates σ hσ).symm
        (((v.1 0).1, -(v.1 0).2), planeToField σ α v.2)) = _
    rw [HermitianModel.minusForm_coordinates, norm_planeToField σ hσ a ha α hα]
    simp [form_apply, sub_neg_eq_add, add_comm]

variable {F : Type u} [Field F] [Finite F]

omit [Finite E] in
private theorem mapped_parameter_missing (s : F ≃+* K) :
    ∀ x : K, x ^ 2 + x ≠ s (parameter F) := by
  intro x hx
  apply parameter_spec F (s.symm x)
  apply s.injective
  simpa using hx

private def parameterRoot (s : F ≃+* K) (hdim : Module.finrank K E = 2) : E :=
  (exists_parameter_root σ hdim (s (parameter F)) (mapped_parameter_missing σ s)).choose

private theorem parameterRoot_spec (s : F ≃+* K) (hdim : Module.finrank K E = 2) :
    parameterRoot σ s hdim ^ 2 + parameterRoot σ s hdim = (s (parameter F) : E) :=
  (exists_parameter_root σ hdim (s (parameter F)) (mapped_parameter_missing σ s)).choose_spec

/-- The actual semilinear isometry from the chosen minus-four space. -/
def minusSpaceEquiv (s : F ≃+* K) (hdim : Module.finrank K E = 2) :
    Space F 1 ≃ₛₗ[(s : F →+* K)] HermitianModel.Space σ hσ :=
  (spaceCoefficientEquiv s 1).trans
    (formHermitianIsometry σ hσ (s (parameter F)) (mapped_parameter_missing σ s)
      (parameterRoot σ s hdim) (parameterRoot_spec σ s hdim) hdim).toLinearEquiv

/-- Preservation of the literal quadratic values, including their signs. -/
theorem minusSpaceEquiv_value (s : F ≃+* K) (hdim : Module.finrank K E = 2)
    (v : Space F 1) :
    HermitianModel.minusForm σ hσ (minusSpaceEquiv σ hσ s hdim v) =
      s (quadraticForm F 2 v) := by
  change HermitianModel.minusForm σ hσ
    ((formHermitianIsometry σ hσ (s (parameter F)) (mapped_parameter_missing σ s)
      (parameterRoot σ s hdim) (parameterRoot_spec σ s hdim) hdim)
      (spaceCoefficientEquiv s 1 v)) = _
  rw [QuadraticMap.IsometryEquiv.map_app, form_spaceCoefficientEquiv]
  rfl

/-- The root furnishing the norm coordinates is a nonfixed field element. -/
theorem exists_nonfixed (s : F ≃+* K) (hdim : Module.finrank K E = 2) :
    ∃ t : E, σ t ≠ t :=
  ⟨parameterRoot σ s hdim,
    root_not_fixed σ (s (parameter F)) (mapped_parameter_missing σ s)
      (parameterRoot σ s hdim) (parameterRoot_spec σ s hdim)⟩

end ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport
