module

public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Descent.ScalarExtension
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.FieldDegree
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Coefficient descent for the actual G₂ automorphism group

An octonion automorphism fixed by coefficient conjugation commutes with that
coefficient map. It therefore restricts, together with its inverse, to the
octonions over the actual fixed subfield. Scalar extension supplies the
inverse group map: the two compositions agree with the identity on all eight
standard basis vectors. Both maps preserve the given octonion multiplication.

This constructs the pure-field fixed-group input to Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.1.4(4), printed p.1171.
The construction works for any field automorphism. At the smallest involutory
finite-field endpoint it gives full G₂(2), as specified on printed p.1191;
the two-residual is treated separately in `EvenFieldFixedResidual.Residual`.
The coefficient action is the actual action from the licensed ATLAS port.
-/

public section

open Atlas.SplitOctonion Atlas.G2.LieAutomorphismExtensions
namespace Atlas.G2.EvenFieldFixedResidual
namespace Descent
variable {F : Type*} [Field F] (σ : F ≃+* F)

private theorem mem_fixedField_iff (x : F) : x ∈ fixedField σ ↔ σ x = x := by
  change (∀ t : Subgroup.zpowers σ, t • x = x) ↔ σ x = x
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h t
    obtain ⟨n, hn⟩ := t.property
    change t.val • x = x
    rw [← hn]
    exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy F σ from h) n

private theorem mapCoefficients_include (x : Carrier (fixedField σ)) :
    mapCoefficients σ (includeCoefficients (fixedField σ) x) =
      includeCoefficients (fixedField σ) x := by
  ext i
  exact (mem_fixedField_iff σ _).mp (x i).property

private theorem fixed_commute (g : (fieldAction σ).fixedSubgroup) (x : Carrier F) :
    mapCoefficients σ (g.val.val x) = g.val.val (mapCoefficients σ x) := by
  have h := fieldEquiv_action σ g.val x
  change (fieldAction σ g.val).val (mapCoefficients σ x) = _ at h
  rw [show fieldAction σ g.val = g.val from (MulAut.mem_fixedSubgroup _ _).mp g.property] at h
  exact h.symm

private theorem image_mem_fixedField (g : (fieldAction σ).fixedSubgroup)
    (x : Carrier (fixedField σ)) (i : Fin 8) :
    g.val.val (includeCoefficients (fixedField σ) x) i ∈ fixedField σ := by
  apply (mem_fixedField_iff σ _).mpr
  have h := fixed_commute σ g (includeCoefficients (fixedField σ) x)
  rw [mapCoefficients_include] at h
  exact congrFun h i

/-- Restriction to vectors whose coefficients lie in the actual fixed field. -/
private noncomputable def restrictLinear (g : (fieldAction σ).fixedSubgroup) :
    Carrier (fixedField σ) →ₗ[fixedField σ] Carrier (fixedField σ) where
  toFun x i := ⟨g.val.val (includeCoefficients (fixedField σ) x) i,
    image_mem_fixedField σ g x i⟩
  map_add' x y := by
    ext i
    change g.val.val (includeCoefficients (fixedField σ) (x+y)) i = _
    rw [map_add, map_add]
    rfl
  map_smul' r x := by
    ext i
    change g.val.val (includeCoefficients (fixedField σ) (r • x)) i = _
    rw [map_smul]
    change g.val.val ((r : F) • includeCoefficients (fixedField σ) x) i = _
    rw [map_smul]
    rfl

@[simp] private theorem include_restrictLinear (g : (fieldAction σ).fixedSubgroup)
    (x : Carrier (fixedField σ)) :
    includeCoefficients (fixedField σ) (restrictLinear σ g x) =
      g.val.val (includeCoefficients (fixedField σ) x) := rfl

/-- Restrict both a fixed automorphism and its inverse. -/
private noncomputable def restrictEquiv (g : (fieldAction σ).fixedSubgroup) :
    Carrier (fixedField σ) ≃ₗ[fixedField σ] Carrier (fixedField σ) where
  toLinearMap := restrictLinear σ g
  invFun := restrictLinear σ g⁻¹
  left_inv x := by
    apply includeCoefficients_injective (fixedField σ)
    change includeCoefficients (fixedField σ)
      (restrictLinear σ g⁻¹ (restrictLinear σ g x)) = _
    rw [include_restrictLinear, include_restrictLinear]
    exact g.val.val.symm_apply_apply _
  right_inv x := by
    apply includeCoefficients_injective (fixedField σ)
    change includeCoefficients (fixedField σ)
      (restrictLinear σ g (restrictLinear σ g⁻¹ x)) = _
    rw [include_restrictLinear, include_restrictLinear]
    exact g.val.val.apply_symm_apply _

/-- Restriction preserves the literal split-octonion multiplication. -/
private noncomputable def restrictAutomorphism (g : (fieldAction σ).fixedSubgroup) :
    Model (fixedField σ) :=
  ⟨restrictEquiv σ g, by
    intro x y
    apply includeCoefficients_injective (fixedField σ)
    change includeCoefficients (fixedField σ) (restrictLinear σ g (mul x y)) = _
    rw [include_restrictLinear, includeCoefficients_mul, automorphism_mul,
      includeCoefficients_mul]
    rfl⟩

@[simp] private theorem restrictAutomorphism_apply (g : (fieldAction σ).fixedSubgroup)
    (x : Carrier (fixedField σ)) :
    includeCoefficients (fixedField σ) ((restrictAutomorphism σ g).val x) =
      g.val.val (includeCoefficients (fixedField σ) x) := rfl

private theorem mapCoefficients_basis (i : Fin 8) :
    mapCoefficients σ (basisVector i : Carrier F) = basisVector i := by
  ext j
  by_cases h : j = i <;> simp [mapCoefficients, basisVector, h]

/-- Scalar extension over the actual fixed field commutes with the coefficient action. -/
private theorem extendAutomorphism_fixed (g : Model (fixedField σ)) :
    fieldAction σ (extendAutomorphism (fixedField σ) g) =
      extendAutomorphism (fixedField σ) g := by
  apply Subtype.ext
  apply (Pi.basisFun F (Fin 8)).ext'
  intro i
  simp only [Pi.basisFun_apply]
  change (fieldAction σ (extendAutomorphism (fixedField σ) g)).val (basisVector i) = _
  have h := fieldEquiv_action σ (extendAutomorphism (fixedField σ) g) (basisVector i)
  rw [mapCoefficients_basis] at h
  change (fieldAction σ (extendAutomorphism (fixedField σ) g)).val (basisVector i) = _ at h
  rw [h]
  change mapCoefficients σ (extendLinear (fixedField σ) g.val.toLinearMap (basisVector i)) =
    extendLinear (fixedField σ) g.val.toLinearMap (basisVector i)
  rw [extendLinear_basis, mapCoefficients_include]

/-- Extension gives an element of the literal coefficient fixed subgroup. -/
private noncomputable def extendFixed (g : Model (fixedField σ)) : (fieldAction σ).fixedSubgroup :=
  ⟨extendAutomorphism (fixedField σ) g,
    (MulAut.mem_fixedSubgroup _ _).mpr (extendAutomorphism_fixed σ g)⟩

@[simp] private theorem restrict_extend (g : Model (fixedField σ)) :
    restrictAutomorphism σ (extendFixed σ g) = g := by
  apply Atlas.Algebra.MultiplicativeLinearAut.ext
  intro x
  apply includeCoefficients_injective (fixedField σ)
  change includeCoefficients (fixedField σ) ((restrictAutomorphism σ (extendFixed σ g)).val x) = _
  rw [restrictAutomorphism_apply]
  exact extendLinear_include (fixedField σ) g.val.toLinearMap x

@[simp] private theorem extend_restrict (g : (fieldAction σ).fixedSubgroup) :
    extendFixed σ (restrictAutomorphism σ g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply (Pi.basisFun F (Fin 8)).ext'
  intro i
  simp only [Pi.basisFun_apply]
  change extendLinear (fixedField σ) (restrictAutomorphism σ g).val.toLinearMap
    (basisVector i) = g.val.val (basisVector i)
  rw [extendLinear_basis]
  change includeCoefficients (fixedField σ) ((restrictAutomorphism σ g).val (basisVector i)) = _
  rw [restrictAutomorphism_apply, includeCoefficients_basis]

end Descent

/-- The full coefficient-fixed G₂ group is G₂ over the actual fixed field.
The forward map restricts fixed coefficients and its inverse extends scalars.
No derived subgroup is taken, including at the binary-field endpoint. -/
noncomputable def coefficientFixedEquiv {F : Type*} [Field F] (σ : F ≃+* F) :
    (fieldAction σ).fixedSubgroup ≃* Model (fixedField σ) where
  toFun := Descent.restrictAutomorphism σ
  invFun := Descent.extendFixed σ
  left_inv := Descent.extend_restrict σ
  right_inv := Descent.restrict_extend σ
  map_mul' g h := by
    apply Atlas.Algebra.MultiplicativeLinearAut.ext
    intro x
    apply Descent.includeCoefficients_injective (fixedField σ)
    change Descent.includeCoefficients (fixedField σ)
      ((Descent.restrictAutomorphism σ (g*h)).val x) = _
    rw [Descent.restrictAutomorphism_apply]
    change g.val.val (h.val.val (Descent.includeCoefficients (fixedField σ) x)) =
      Descent.includeCoefficients (fixedField σ)
        ((Descent.restrictAutomorphism σ g).val ((Descent.restrictAutomorphism σ h).val x))
    rw [Descent.restrictAutomorphism_apply, Descent.restrictAutomorphism_apply]

variable {F : Type*} [Field F] (σ : F ≃+* F)

/-- Descent intertwines the original action with the actual coefficient inclusion. -/
@[simp] theorem coefficientFixedEquiv_apply (g : (fieldAction σ).fixedSubgroup)
    (x : Carrier (fixedField σ)) :
    Descent.includeCoefficients (fixedField σ) ((coefficientFixedEquiv σ g).val x) =
      g.val.val (Descent.includeCoefficients (fixedField σ) x) := by
  exact Descent.restrictAutomorphism_apply σ g x

/-- The inverse equivalence is scalar extension along that same inclusion. -/
@[simp] theorem coefficientFixedEquiv_symm_apply (g : Model (fixedField σ))
    (x : Carrier (fixedField σ)) :
    ((coefficientFixedEquiv σ).symm g).val.val
        (Descent.includeCoefficients (fixedField σ) x) =
      Descent.includeCoefficients (fixedField σ) (g.val x) := by
  change Descent.extendLinear (fixedField σ) g.val.toLinearMap
    (Descent.includeCoefficients (fixedField σ) x) = _
  exact Descent.extendLinear_include (fixedField σ) g.val.toLinearMap x

end Atlas.G2.EvenFieldFixedResidual
