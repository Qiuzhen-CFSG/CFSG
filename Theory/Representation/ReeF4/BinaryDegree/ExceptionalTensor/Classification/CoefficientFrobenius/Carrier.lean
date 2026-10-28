module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Embedding
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius.Transport

/-!
# Coefficient automorphisms of the concrete closed F4 carrier

Entrywise coefficient transport preserves the integral root matrices and sends
`x_r(t)` to `x_r(σ(t))`. Subgroup-closure induction therefore restricts the
ambient general-linear coefficient automorphism to the actual closed F4
carrier. The resulting automorphism acts coefficientwise on the presented
variety coordinates, as required for polynomial transport of rational actions.

Source: the integral Chevalley construction and GLS3, Remark 2.8.8. These are
point-group automorphisms; arbitrary inverse field automorphisms are not
asserted to be polynomial morphisms.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.CoefficientTransport
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
noncomputable section

omit [IsAlgClosed F] in
private theorem glPoint_ext_matrix {n : ℕ}
    {x y : Variety.Point (glVariety n : Variety F)}
    (h : ∀ i j, x.val (Sum.inl (i, j)) = y.val (Sum.inl (i, j))) : x = y := by
  apply (glPointEquiv n).injective
  apply Units.ext
  ext i j
  exact h i j

omit [IsAlgClosed F] in
private theorem rootCurve_coefficients (σ : F →+* F) (r : F4Chevalley.Root) (t : F) :
    Units.map σ.mapMatrix.toMonoidHom (F4Chevalley.rootCurve r t) =
      F4Chevalley.rootCurve r (σ t) := by
  apply Units.ext
  change (↑(F4Chevalley.rootCurve r t) :
    Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F).map σ = _
  rw [F4Chevalley.rootCurve_matrix_formula, F4Chevalley.rootCurve_matrix_formula]
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    specializeMatrix, Matrix.one_apply, apply_ite σ]

private theorem ambientRoot_coordinate (r : F4Chevalley.Root) (t : F)
    (i j : Fin (Module.finrank F (F4Chevalley.BasisIndex → F))) :
    ((F4Chevalley.ambientRootMorphism r).onPoints (kPlusPoint t)).val (Sum.inl (i, j)) =
      (F4Chevalley.rootCurve r t : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)
        ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm i)
        ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm j) := by
  rw [F4Chevalley.ambientRootMorphism_apply, generalLinearRepresentationPoint_matrix]
  simp [carrierBasis, rootPointRepresentation, Module.Basis.reindex_apply]
  rfl

theorem ambientCoefficient_root (σ : F ≃+* F) (r : F4Chevalley.Root) (t : F) :
    (glCoefficientAction σ _).equiv
      ((F4Chevalley.ambientRootMorphism r).onPoints (kPlusPoint t)) =
      (F4Chevalley.ambientRootMorphism r).onPoints (kPlusPoint (σ t)) := by
  apply glPoint_ext_matrix
  intro i j
  rw [(glCoefficientAction σ _).coordinate, ambientRoot_coordinate, ambientRoot_coordinate]
  exact congrArg (fun x : (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ =>
    x.val ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm i)
      ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm j))
    (rootCurve_coefficients (σ : F →+* F) r t)

theorem ambientCoefficient_mem (σ : F ≃+* F)
    {g : Variety.Point (F4Chevalley.Ambient F)}
    (hg : g ∈ F4Chevalley.ambientCarrierSubgroup (k := F)) :
    (glCoefficientAction σ _).equiv g ∈ F4Chevalley.ambientCarrierSubgroup (k := F) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hg
      obtain ⟨t, rfl⟩ := hr
      rw [← kPlusPoint_coordinate t, ambientCoefficient_root]
      exact F4Chevalley.ambientRoot_mem_carrier r _
  | one => simp
  | mul x y _ _ hx hy =>
      simpa only [map_mul] using (F4Chevalley.ambientCarrierSubgroup (k := F)).mul_mem hx hy
  | inv x _ hx =>
      simpa only [map_inv] using (F4Chevalley.ambientCarrierSubgroup (k := F)).inv_mem hx

private theorem glCoefficientAction_symm (σ : F ≃+* F) (n : ℕ) :
    (glCoefficientAction σ n).equiv.symm = (glCoefficientAction σ.symm n).equiv := by
  ext g
  apply Variety.Point.ext
  ext i
  rw [(glCoefficientAction σ n).symm_coordinate, (glCoefficientAction σ.symm n).coordinate]

/-- The genuine coefficient automorphism of the closed F4 point group. -/
def carrierCoefficientAction (σ : F ≃+* F) :
    CoefficientAction σ (F4Chevalley.Carrier (k := F)) where
  equiv :=
    { toFun := fun g => (F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv.symm
        ⟨(glCoefficientAction σ _).equiv
          ((F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv g).val,
          ambientCoefficient_mem σ ((F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv g).property⟩
      invFun := fun g => (F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv.symm
        ⟨(glCoefficientAction σ _).equiv.symm
          ((F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv g).val,
          by rw [glCoefficientAction_symm]; exact
            ambientCoefficient_mem σ.symm
              ((F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv g).property⟩
      left_inv := by intro g; simp
      right_inv := by intro g; simp
      map_mul' := by
        intro x y
        apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
        change (glCoefficientAction σ _).equiv (_ * _) =
          (glCoefficientAction σ _).equiv _ * (glCoefficientAction σ _).equiv _
        exact map_mul _ _ _ }
  coordinate := by
    intro g i
    exact (glCoefficientAction σ _).coordinate
      ((F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv g).val i

@[simp] theorem carrierCoefficient_root (σ : F ≃+* F)
    (r : F4Chevalley.Root) (t : F) :
    (carrierCoefficientAction σ).equiv (algebraicRootElement r t) =
      algebraicRootElement r (σ t) := by
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  change (glCoefficientAction σ _).equiv
    ((F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
      (algebraicRootElement r t)) = _
  rw [algebraicRootElement, F4Chevalley.rootMorphism_inclusion_apply,
    ambientCoefficient_root]
  exact (F4Chevalley.rootMorphism_inclusion_apply r (kPlusPoint (σ t))).symm

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius
