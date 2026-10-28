module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Invariant
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ReferenceData
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Generators
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.EdgeImage
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.GroupTheory.Schreier

/-!
# Determinant-one action on the geometric point submodule

The invariant six-dimensional binary submodule carries the specified quadratic
field structure.  This module constructs the actual field-linear action of the
literal point stabilizer on its three-dimensional field coordinates, proves
that its determinant character is trivial through the native M22 point
stabilizer quotient, and records the resulting natural-action identity.

The determinant-one action, certified edge-word images, and native Schreier
calculation below provide the actual identification with the matrix group
`SL₃(4)`. The retained source diagnostics guide these finite certificates but
are not used as Lean theorems.
Source context: James (1973), Lemma 8.3, as used in Aschbacher--Smith H.12.1,
printed pp.393--394.
-/


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Matrix
open scoped MatrixGroups
abbrev F := Representation.SL2FourNatural.F
abbrev W := Fin 3 → F
abbrev G := Sporadic.Mathieu.M22TripleCover.Uniqueness.pointStabilizer
abbrev SL := Matrix.SpecialLinearGroup (Fin 3) F

lemma test_mem (g : G) (v : W) : pointRepresentation g (naturalInclusion v) ∈ starAnnihilator := by
  exact starAnnihilator_invariant g (invariantCoordinates v).property

lemma scalar_decomposition (a : F) (x : F) :
    a * x = a.re • x + a.im • ((QuadraticAlgebra.omega : F) * x) := by
  have ha : a = a.re • (1 : F) + a.im • (QuadraticAlgebra.omega : F) := by
    change a = a.re • (⟨1,0⟩ : F) + a.im • (⟨0,1⟩ : F)
    rw [show a = ⟨a.re,a.im⟩ by rfl]
    ext <;> simp [QuadraticAlgebra.smul_mk]
  rw [ha, add_mul]
  simp [Algebra.smul_def]
  rw [mul_assoc]

lemma vector_scalar_decomposition (a : F) (v : W) :
    a • v = a.re • v + a.im • ((QuadraticAlgebra.omega : F) • v) := by
  funext i
  change a * v i = _
  rw [scalar_decomposition]
  rfl

lemma naturalInclusion_smul (a : F) (v : W) :
    naturalInclusion (a • v) =
      a.re • naturalInclusion v + a.im • pointRepresentation pointScalar (naturalInclusion v) := by
  rw [vector_scalar_decomposition, map_add, map_smul, map_smul, naturalInclusion_scalar]

noncomputable def actionValue (g : G) (v : W) : W :=
  invariantCoordinates.symm ⟨pointRepresentation g (naturalInclusion v), (by
    change pointRepresentation g (naturalInclusion v) ∈ starAnnihilator
    exact test_mem g v)⟩

lemma naturalInclusion_actionValue (g : G) (v : W) :
    naturalInclusion (actionValue g v) = pointRepresentation g (naturalInclusion v) := by
  change (invariantCoordinates (invariantCoordinates.symm _)).val = _
  rw [invariantCoordinates.apply_symm_apply]

lemma pointRepresentation_scalar_commute (g : G) (x : BinarySpace) :
    pointRepresentation g (pointRepresentation pointScalar x) =
      pointRepresentation pointScalar (pointRepresentation g x) := by
  have hc : g * pointScalar = pointScalar * g := by
    apply Subtype.ext
    change (g : M22TripleCover) * scalar = scalar * (g : M22TripleCover)
    exact Subgroup.mem_center_iff.mp scalar_mem_center g
  have hh := congrArg (fun y : G => pointRepresentation y x) hc
  simpa only [map_mul, Module.End.mul_apply] using hh

noncomputable def actionMap (g : G) : W →ₗ[F] W :=
  { toFun := actionValue g
    map_add' := by
      intro v w
      apply naturalInclusion_injective
      rw [naturalInclusion_actionValue g (v + w)]
      rw [naturalInclusion.map_add v w]
      rw [map_add (pointRepresentation g)]
      rw [naturalInclusion.map_add (actionValue g v) (actionValue g w)]
      rw [naturalInclusion_actionValue g v, naturalInclusion_actionValue g w]
    map_smul' := by
      intro a v
      apply naturalInclusion_injective
      rw [naturalInclusion_actionValue g (a • v)]
      rw [naturalInclusion_smul]
      rw [naturalInclusion_smul]
      rw [map_add, map_smul, map_smul, pointRepresentation_scalar_commute]
      rw [naturalInclusion_actionValue]
      change a.re • _ + a.im • _ = a.re • _ + a.im • _
      rfl }



noncomputable def actionEquiv (g : G) : W ≃ₗ[F] W :=
  { toFun := actionValue g
    invFun := actionValue g⁻¹
    left_inv := by
      intro v
      apply naturalInclusion_injective
      calc
        naturalInclusion (actionValue g⁻¹ (actionValue g v)) =
            pointRepresentation g⁻¹ (naturalInclusion (actionValue g v)) :=
          naturalInclusion_actionValue _ _
        _ = pointRepresentation g⁻¹ (pointRepresentation g (naturalInclusion v)) := by
          rw [naturalInclusion_actionValue]
        _ = naturalInclusion v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          simp
    right_inv := by
      intro v
      apply naturalInclusion_injective
      calc
        naturalInclusion (actionValue g (actionValue g⁻¹ v)) =
            pointRepresentation g (naturalInclusion (actionValue g⁻¹ v)) :=
          naturalInclusion_actionValue _ _
        _ = pointRepresentation g (pointRepresentation g⁻¹ (naturalInclusion v)) := by
          rw [naturalInclusion_actionValue]
        _ = naturalInclusion v := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          simp
    map_add' := (actionMap g).map_add
    map_smul' := (actionMap g).map_smul }

noncomputable def actionEquivHom : G →* (W ≃ₗ[F] W) where
  toFun := actionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply naturalInclusion_injective
    change naturalInclusion (actionValue (1 : G) v) = naturalInclusion v
    rw [naturalInclusion_actionValue]
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    apply naturalInclusion_injective
    change naturalInclusion (actionValue (g * h) v) =
      naturalInclusion (actionValue g (actionValue h v))
    rw [naturalInclusion_actionValue, naturalInclusion_actionValue]
    rw [map_mul, Module.End.mul_apply, ← naturalInclusion_actionValue h v]

noncomputable def actionHom : G →* LinearMap.GeneralLinearGroup F W :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F W).symm.toMonoidHom.comp actionEquivHom

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel

namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Matrix
open scoped MatrixGroups
noncomputable def actionMatrixHom : G →* Matrix.GeneralLinearGroup (Fin 3) F :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp actionHom

lemma actionMatrixHom_toLin (g : G) :
    Matrix.GeneralLinearGroup.toLin (actionMatrixHom g) = actionHom g := by
  simp [actionMatrixHom]

lemma actionMatrixHom_apply (g : G) (v : W) :
    (actionMatrixHom g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = actionValue g v := by
  have h := congrArg (fun f : LinearMap.GeneralLinearGroup F W => LinearMap.GeneralLinearGroup.toLinearEquiv f v) (actionMatrixHom_toLin g)
  rw [actionMatrixHom_toLin] at h
  change (actionEquiv g) v = actionValue g v at h
  have hm := Matrix.GeneralLinearGroup.toLin_apply (actionMatrixHom g) v
  rw [actionMatrixHom_toLin] at hm
  change (actionEquiv g) v = (actionMatrixHom g : Matrix (Fin 3) (Fin 3) F) *ᵥ v at hm
  exact hm.symm.trans h

noncomputable def detHom : G →* Fˣ := Matrix.GeneralLinearGroup.det.comp actionMatrixHom

example (g : G) : detHom g = Matrix.GeneralLinearGroup.det (actionMatrixHom g) := rfl

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Matrix
open scoped MatrixGroups
lemma actionValue_pointScalar (v : W) :
    actionValue pointScalar v = (QuadraticAlgebra.omega : F) • v := by
  apply naturalInclusion_injective
  rw [naturalInclusion_actionValue, naturalInclusion_scalar]

lemma actionMatrix_pointScalar :
    (actionMatrixHom pointScalar : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun _ : Fin 3 => (QuadraticAlgebra.omega : F)) := by
  apply Matrix.mulVec_injective
  funext v
  rw [actionMatrixHom_apply, actionValue_pointScalar]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

lemma detHom_pointScalar : detHom pointScalar = 1 := by
  apply Units.ext
  change Matrix.det (actionMatrixHom pointScalar : Matrix (Fin 3) (Fin 3) F) = 1
  rw [actionMatrix_pointScalar, Matrix.det_diagonal]
  decide +kernel

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
noncomputable def pointQuotient : G →* MulAction.stabilizer M22 (1 : Fin 22) where
  toFun g := ⟨quotientMap g.val, g.property⟩
  map_one' := by apply Subtype.ext; simp [quotientMap]
  map_mul' g h := by apply Subtype.ext; simp

lemma detHom_eq_one_of_pointQuotient_eq_one {g : G}
    (hg : pointQuotient g = 1) : detHom g = 1 := by
  have hq : quotientMap g.val = 1 := by
    exact congrArg Subtype.val hg
  have hc : g.val ∈ Subgroup.center M22TripleCover := by
    rw [← quotientMap_ker]
    exact MonoidHom.mem_ker.mpr hq
  rw [center_eq_zpowers] at hc
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
  have heq : g = pointScalar ^ n := by
    apply Subtype.ext
    exact hn.symm
  rw [heq, map_zpow, detHom_pointScalar, one_zpow]
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
noncomputable def detQuotient (hPQ : Function.Surjective pointQuotient) :
    (MulAction.stabilizer M22 (1 : Fin 22)) →* Fˣ :=
  pointQuotient.liftOfSurjective hPQ ⟨detHom, by
    intro g hg
    exact MonoidHom.mem_ker.mpr (detHom_eq_one_of_pointQuotient_eq_one hg)
  ⟩

lemma detQuotient_comp (hPQ : Function.Surjective pointQuotient) (g : G) :
    detQuotient hPQ (pointQuotient g) = detHom g := by
  exact MonoidHom.liftOfRightInverse_comp_apply pointQuotient
    (Function.surjInv hPQ) (Function.rightInverse_surjInv hPQ)
    ⟨detHom, by intro x hx; exact MonoidHom.mem_ker.mpr (detHom_eq_one_of_pointQuotient_eq_one hx)⟩ g

lemma detHom_eq_one_of_perfect (hPQ : Function.Surjective pointQuotient)
    (hperf : Group.IsPerfect (MulAction.stabilizer M22 (1 : Fin 22))) :
    ∀ g : G, detHom g = 1 := by
  intro g
  rw [← detQuotient_comp hPQ g]
  have hm := Group.IsPerfect.mem_commutator (G := MulAction.stabilizer M22 (1 : Fin 22))
    (g := pointQuotient g)
  have hk := (Abelianization.commutator_subset_ker (detQuotient hPQ)) hm
  exact MonoidHom.mem_ker.mp hk
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
noncomputable def slModuleHom (hdet : ∀ g : G, detHom g = 1) :
    G →* SpecialLinearGroup F W where
  toFun g := ⟨actionEquiv g, by
    have hd := congrArg Units.val (hdet g)
    change Matrix.det (actionMatrixHom g : Matrix (Fin 3) (Fin 3) F) = 1 at hd
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det ((actionEquiv g : W ≃ₗ[F] W) : W →ₗ[F] W) = 1
    rw [show (actionEquiv g : W →ₗ[F] W) =
      Matrix.toLin' (actionMatrixHom g : Matrix (Fin 3) (Fin 3) F) by
        apply LinearMap.ext
        intro v
        have hm := Matrix.GeneralLinearGroup.toLin_apply (actionMatrixHom g) v
        rw [actionMatrixHom_toLin] at hm
        change (actionEquiv g) v = _ at hm
        simpa [Matrix.mulVecLin_apply] using hm]
    rw [LinearMap.det_toLin']
    exact hd
  ⟩
  map_one' := by apply Subtype.ext; exact (actionEquivHom.map_one)
  map_mul' g h := by apply Subtype.ext; exact (actionEquivHom.map_mul g h)

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
noncomputable def slHom (hdet : ∀ g : G, detHom g = 1) : G →* SL :=
  (Matrix.SpecialLinearGroup.toLin'_equiv (R := F) (n := Fin 3)).symm.toMonoidHom.comp
    (slModuleHom hdet)

lemma slHom_actionMatrix (hdet : ∀ g : G, detHom g = 1) (g : G) :
    ((slHom hdet g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (actionMatrixHom g : Matrix (Fin 3) (Fin 3) F) := by
  change (((Matrix.SpecialLinearGroup.toLin'_equiv (R := F) (n := Fin 3)).symm (slModuleHom hdet g)) : Matrix (Fin 3) (Fin 3) F) = _
  change LinearMap.toMatrix' ((actionEquiv g : W ≃ₗ[F] W) : W →ₗ[F] W) = _
  apply Matrix.mulVec_injective
  funext v
  rw [LinearMap.toMatrix'_mulVec]
  change (actionEquiv g) v = _
  exact (actionMatrixHom_apply g v).symm.trans rfl

lemma slHom_natural_action (hdet : ∀ g : G, detHom g = 1) (g : G) (v : W) :
    pointRepresentation g (naturalInclusion v) =
      naturalInclusion (Matrix.mulVec (slHom hdet g : Matrix (Fin 3) (Fin 3) F) v) := by
  rw [← naturalInclusion_actionValue, ← actionMatrixHom_apply]
  rw [slHom_actionMatrix]

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
lemma pointQuotient_surjective : Function.Surjective pointQuotient := by
  intro h
  obtain ⟨x, hx⟩ := quotientMap_surjective h.val
  have hfix : x ∈ pointStabilizer := by
    change quotientMap x ∈ MulAction.stabilizer M22 (1 : Fin 22)
    simpa [← hx] using h.property
  exact ⟨⟨x, hfix⟩, by apply Subtype.ext; exact hx⟩

lemma detHom_eq_one (g : G) : detHom g = 1 := by
  apply detHom_eq_one_of_perfect pointQuotient_surjective
    (MathieuCode.m22PointStabilizer_perfect 1) g
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Matrix
open scoped MatrixGroups

/-- The determinant-one field-linear action on the invariant three-space. -/
noncomputable def pointSLHom : G →* SL := slHom detHom_eq_one

lemma pointSLHom_natural_action (g : G) (v : W) :
    pointRepresentation g (naturalInclusion v) =
      naturalInclusion (Matrix.mulVec (pointSLHom g : Matrix (Fin 3) (Fin 3) F) v) :=
  slHom_natural_action detHom_eq_one g v

private lemma referenceSL_card : Nat.card SL = 60480 := by
  have hp := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  have hcenter := Atlas.ExceptionalSupport.card_sl_center
    (ι := Fin 3) (F := F)
  rw [show Nat.card F = 4 by
    rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]] at hp
  norm_num [Fin.prod_univ_succ] at hp
  rw [show Nat.card F = 4 by
    rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]] at hcenter
  norm_num at hcenter
  have hq : Nat.card (SL ⧸ Subgroup.center SL) = 20160 := by
    change Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 20160
    rw [Nat.card_eq_fintype_card]
    omega
  have hc : Nat.card (Subgroup.center SL) = 3 := by
    rw [Nat.card_eq_fintype_card]
    exact hcenter
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
    hq, hc]

/-- The actual point-stabilizer identification with the specified `SL₃(4)`. -/
noncomputable def pointStabilizerEquiv : G ≃* SL :=
  MulEquiv.ofBijective pointSLHom
    ((surjective_of_natural_action pointSLHom pointSLHom_natural_action).bijective_of_nat_card_le
      (by rw [pointStabilizer_card, referenceSL_card]))

lemma pointStabilizerEquiv_natural_action (g : G) (v : W) :
    pointRepresentation g (naturalInclusion v) =
      naturalInclusion ((pointStabilizerEquiv g).val *ᵥ v) := by
  simpa [pointStabilizerEquiv] using pointSLHom_natural_action g v

lemma pointStabilizerEquiv_pointScalar :
    pointStabilizerEquiv pointScalar = Reference.scalar := by
  apply Subtype.ext
  change (pointSLHom pointScalar : Matrix (Fin 3) (Fin 3) F) = _
  rw [show (pointSLHom pointScalar : Matrix (Fin 3) (Fin 3) F) =
    (actionMatrixHom pointScalar : Matrix (Fin 3) (Fin 3) F) by
      exact slHom_actionMatrix detHom_eq_one pointScalar, actionMatrix_pointScalar]
  rfl

private def nativeSchreierClosure : Subgroup M22TripleCover :=
  (Subgroup.closure schreierGenerators).map pointStabilizer.subtype

private lemma nativeSchreier_mem (i : Fin 22) (j : Fin 2) :
    (schreierGenerator i j : M22TripleCover) ∈ nativeSchreierClosure := by
  apply Subgroup.mem_map.mpr
  exact ⟨schreierGenerator i j,
    Subgroup.subset_closure ⟨(i, j), rfl⟩, rfl⟩

private def nativeSchreierProperty (g : M22TripleCover) : Prop :=
  ∀ i : Fin 22,
    (transversal (corePermutationAction g i))⁻¹ * g * transversal i ∈
      nativeSchreierClosure

private lemma schreier_inverse_identity {H : Type*} [Group H]
    (A B g : H) : (A⁻¹ * g * B)⁻¹ = B⁻¹ * g⁻¹ * A := by
  group

private lemma schreier_product_identity {H : Type*} [Group H]
    (A B C g h : H) :
    A⁻¹ * (g * h) * C = (A⁻¹ * g * B) * (B⁻¹ * h * C) := by
  group

private lemma nativeSchreierProperty_one : nativeSchreierProperty 1 := by
  intro i
  simp

private lemma nativeSchreierProperty_generator (j : Fin 2) :
    nativeSchreierProperty (ambientGenerator j) := by
  intro i
  rw [ambientGenerator_action]
  change (schreierGenerator i j : M22TripleCover) ∈ nativeSchreierClosure
  exact nativeSchreier_mem i j

private lemma nativeSchreierProperty_inv {g : M22TripleCover}
    (hg : nativeSchreierProperty g) : nativeSchreierProperty g⁻¹ := by
  intro i
  have hgi : corePermutationAction g (corePermutationAction g⁻¹ i) = i := by
    have h := congrArg (fun p : Equiv.Perm (Fin 22) => p i)
      (show corePermutationAction (g * g⁻¹) = 1 by simp)
    simpa only [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h
  have hi := hg (corePermutationAction g⁻¹ i)
  have hm := nativeSchreierClosure.inv_mem hi
  rw [hgi] at hm
  rw [schreier_inverse_identity] at hm
  exact hm

private lemma nativeSchreierProperty_mul {g h : M22TripleCover}
    (hg : nativeSchreierProperty g) (hh : nativeSchreierProperty h) :
    nativeSchreierProperty (g * h) := by
  intro i
  have hm := nativeSchreierClosure.mul_mem (hg (corePermutationAction h i)) (hh i)
  rw [map_mul]
  rw [Equiv.Perm.mul_apply]
  change (transversal (corePermutationAction g (corePermutationAction h i)))⁻¹ * g *
      transversal (corePermutationAction h i) *
      ((transversal (corePermutationAction h i))⁻¹ * h * transversal i) ∈
    nativeSchreierClosure at hm
  rw [schreier_product_identity]
  exact hm

private lemma nativeSchreierProperty_all (g : M22TripleCover) :
    nativeSchreierProperty g := by
  have hg : g ∈ Subgroup.closure {coreGeneratorA, coreGeneratorB} := by
    rw [coreGenerators_closure_eq_top]
    trivial
  refine Subgroup.closure_induction''
    (p := fun x _ => nativeSchreierProperty x) ?_ ?_ ?_ ?_ hg
  · intro x hx
    rcases hx with (rfl | rfl)
    · exact nativeSchreierProperty_generator 0
    · exact nativeSchreierProperty_generator 1
  · intro x hx
    rcases hx with (rfl | rfl)
    · exact nativeSchreierProperty_inv (nativeSchreierProperty_generator 0)
    · exact nativeSchreierProperty_inv (nativeSchreierProperty_generator 1)
  · exact nativeSchreierProperty_one
  · intro x y hx hy ihx ihy
    exact nativeSchreierProperty_mul ihx ihy

/-- The actual forty-four Schreier words generate the native point stabilizer. -/
lemma closure_schreierGenerators_eq_top :
    Subgroup.closure schreierGenerators = ⊤ := by
  apply top_unique
  intro g hg
  have hm := nativeSchreierProperty_all (g : M22TripleCover) 1
  have hfix : corePermutationAction (g : M22TripleCover) 1 = 1 := g.property
  rw [hfix, transversal_one] at hm
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hm
  have hxeq' : x = g := by
    apply Subtype.ext
    simpa using hxeq
  simpa [hxeq'] using hx

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
