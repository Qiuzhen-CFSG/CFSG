module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.Data
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Transport

/-!
# Scalar restriction for the dual induced point-module filtration

The original central scalar acts by omega squared on the dual constituent
and hence on the entire induced module. Its square acts by omega. Every
binary invariant subspace is therefore F₄-stable, including the invariant
subspaces in each literal quotient of a filtration. Restriction of scalars
preserves simplicity and doubles the quotient dimensions.

`restrict_filtration` proves this for any action containing multiplication
by omega. The application to the actual dual coordinate representation is
`dual_factorDegreeFiltration_of_field` in the parent module. It removes only
the scalar-restriction obligation; constructing the field filtration remains
necessary. Source context: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15–16, and Theorem 6.6/Table 6.7.
-/

@[expose] public noncomputable section
open Representation
open Representation.SL3FourLocalCatalogue
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration
open Uniqueness Uniqueness.PointRestriction.PointModel

section
variable {G V : Type*} [Group G] [AddCommGroup V] [Module F V]
  [Module (ZMod 2) V] [IsScalarTower (ZMod 2) F V]
  (ρ : Representation F G V) (z : G)
  (hz : ∀ v, ρ z v = (QuadraticAlgebra.omega : F) • v)

/-- Multiplication by omega forces every binary invariant subspace to be F₄-linear. -/
def scalarSubrepresentationEquiv :
    Subrepresentation (restrictScalars (k := ZMod 2) ρ) ≃o Subrepresentation ρ := by
  refine {
    toFun := fun U => {
      toSubmodule := {
        carrier := U
        zero_mem' := U.toSubmodule.zero_mem
        add_mem' := U.toSubmodule.add_mem
        smul_mem' := ?_ }
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    invFun := fun U => {
      toSubmodule := U.toSubmodule.restrictScalars (ZMod 2)
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := fun {_ _} => Iff.rfl }
  · intro r v hv
    have he : r • v = r.re • v + r.im • ((QuadraticAlgebra.omega : F) • v) := by
      conv_lhs => rw [show r = algebraMap (ZMod 2) F r.re +
        r.im • (QuadraticAlgebra.omega : F) from
          QuadraticAlgebra.mk_eq_add_smul_omega r.re r.im]
      rw [add_smul, algebraMap_smul, smul_assoc]
    rw [he, ← hz]
    exact U.toSubmodule.add_mem (U.toSubmodule.smul_mem _ hv)
      (U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule z hv))
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl

include hz in
/-- A group element acting by omega makes scalar restriction preserve simplicity. -/
lemma scalar_restrict_irreducible [IsIrreducible ρ] :
    IsIrreducible (restrictScalars (k := ZMod 2) ρ) :=
  (scalarSubrepresentationEquiv ρ z hz).isSimpleOrder_iff.mpr inferInstance
end

/-- Restrict an actual filtration, transporting its subspaces and literal quotients. -/
theorem restrict_filtration {G V : Type*} [Group G] [AddCommGroup V] [Module F V]
    {D E : Set ℕ} {ρ : Representation F G V} (z : G)
    (hdeg : ∀ d ∈ D, 2 * d ∈ E) (h : FactorDegreeFiltration D ρ) :
    ∀ [Module (ZMod 2) V] [IsScalarTower (ZMod 2) F V],
    (∀ v, ρ z v = (QuadraticAlgebra.omega : F) • v) →
    FactorDegreeFiltration E (restrictScalars (k := ZMod 2) ρ) := by
  induction h with
  | zero τ =>
    intro _ _ _
    exact .zero _
  | @step X _ _ τ S previous simple degree ih =>
    intro _ _ hz
    let T : Subrepresentation (restrictScalars (k := ZMod 2) τ) := {
      toSubmodule := S.toSubmodule.restrictScalars (ZMod 2)
      apply_mem_toSubmodule g _ hv := S.apply_mem_toSubmodule g hv }
    have hzs : ∀ v, S.toRepresentation z v = (QuadraticAlgebra.omega : F) • v := by
      intro v
      apply Subtype.ext
      exact hz v
    have hp := ih hzs
    let es : S.toSubmodule ≃ₗ[ZMod 2] T.toSubmodule :=
      ((Submodule.restrictScalarsEquiv (ZMod 2) F X S.toSubmodule).restrictScalars (ZMod 2)).symm
    have hpT : FactorDegreeFiltration E T.toRepresentation :=
      hp.transport (MonoidHom.id G) (fun x => ⟨x, rfl⟩) T.toRepresentation es (fun _ _ => rfl)
    let eq : (X ⧸ T.toSubmodule) ≃ₗ[ZMod 2] (X ⧸ S.toSubmodule) :=
      Submodule.Quotient.restrictScalarsEquiv (ZMod 2) S.toSubmodule
    let eqr : Representation.RepEquiv T.quotientRepresentation
        (restrictScalars (k := ZMod 2) S.quotientRepresentation) := {
      toLinearEquiv := eq
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        induction v using Submodule.Quotient.induction_on with
        | H v => rfl }
    have hzq : ∀ v, S.quotientRepresentation z v = (QuadraticAlgebra.omega : F) • v := by
      intro v
      induction v using Submodule.Quotient.induction_on with
      | H v =>
        change S.toSubmodule.mkQ (τ z v) =
          (QuadraticAlgebra.omega : F) • S.toSubmodule.mkQ v
        rw [hz, map_smul]
    let := simple
    refine .step T hpT (eqr.irreducible_of_euqiv (scalar_restrict_irreducible _ z hzq)) ?_
    rw [eq.finrank_eq]
    have hd := Module.finrank_mul_finrank (ZMod 2) F (X ⧸ S.toSubmodule)
    rw [QuadraticAlgebra.finrank_eq_two] at hd
    rw [← hd]
    exact hdeg _ degree

lemma scalar_permutation : corePermutationAction scalar = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [corePermutationAction_ker_eq_center]
  exact scalar_mem_center

lemma cocycle_scalar (i : Fin 22) : cocycle scalar i = PointRestriction.pointScalar := by
  apply Subtype.ext
  change (transversal (corePermutationAction scalar i))⁻¹ * scalar * transversal i = scalar
  rw [scalar_permutation, Equiv.Perm.one_apply]
  rw [(Subgroup.mem_center_iff.mp scalar_mem_center (transversal i)⁻¹)]
  simp

lemma constituent_dual_scalar (v : Representation.SL3FourLocalCatalogue.W) :
    constituent .dual Reference.scalar v = (QuadraticAlgebra.omega : F)^2 • v := by
  have h : ((Matrix.SpecialLinearGroup.inverseTranspose Reference.scalar).val) =
      Matrix.diagonal (fun _ : Fin 3 => (QuadraticAlgebra.omega : F)^2) := by decide +kernel
  change ((Matrix.SpecialLinearGroup.inverseTranspose Reference.scalar).val).mulVec v = _
  rw [h, Matrix.diagonal_const_mulVec]

/-- The original central scalar acts by the inverse field scalar on the dual. -/
lemma fieldRepresentation_dual_scalar (v : Space) :
    fieldRepresentation .dual scalar v = (QuadraticAlgebra.omega : F)^2 • v := by
  funext i
  have h := action_apply .dual scalar v i
  rw [scalar_permutation, Equiv.Perm.one_apply, cocycle_scalar,
    PointRestriction.PointModel.pointStabilizerEquiv_pointScalar] at h
  exact h.trans (constituent_dual_scalar (v i))

/-- Squaring the original central element supplies multiplication by omega. -/
lemma fieldRepresentation_dual_scalar_sq (v : Space) :
    fieldRepresentation .dual (scalar ^ 2) v = (QuadraticAlgebra.omega : F) • v := by
  rw [pow_two, map_mul, Module.End.mul_apply,
    fieldRepresentation_dual_scalar, fieldRepresentation_dual_scalar, smul_smul]
  have h : (QuadraticAlgebra.omega : F)^2 * (QuadraticAlgebra.omega : F)^2 =
      (QuadraticAlgebra.omega : F) := by decide +kernel
  rw [h]

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration
