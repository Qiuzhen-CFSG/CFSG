module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ComponentTensor.Tensor
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ComponentTensor.Refinement
public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The compatible determinant form on the actual tensor module

The two degree-two tensor factors are constructed over the given finite
field. Their perfect actions have determinant one, so the tensor determinant
is invariant. Absolute irreducibility makes its nonzero polar form a scalar
multiple of the given nondegenerate invariant form; rescaling gives exactly
that polar form. This is the actual quadratic realization used for the
component-product branch of Aschbacher--Smith G.4.9, pp.341--342.
-/

public section
noncomputable section
open scoped TensorProduct
open Matrix
namespace Representation.ComponentTensor
open QuadraticFourGroup.TensorClassification
variable {F G H V : Type*} [Field F] [Group G] [Group H]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem invariant_form_scalar (ρ : Representation F G V)
    [ρ.IsIrreducible] [ρ.IsAbsolutelyIrreducible]
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (hBinv : ∀g v w,B (ρ g v) (ρ g w)=B v w)
    (C : LinearMap.BilinForm F V) (hCinv : ∀g v w,C (ρ g v) (ρ g w)=C v w) :
    ∃c:F,C=c•B := by
  let T : Module.End F V := (B.toDual hB).symm.toLinearMap.comp C
  have hT (v w:V) : B (T v) w=C v w :=
    LinearMap.BilinForm.apply_toDual_symm_apply (hB:=hB) (C v) w
  let f : ρ.IntertwiningMap ρ := {
    toLinearMap := T
    isIntertwining' g := by
      ext v
      apply (B.toDual hB).injective
      ext w
      obtain ⟨w,rfl⟩ := (ρ.apply_bijective g).surjective w
      change B (T (ρ g v)) (ρ g w)=B (ρ g (T v)) (ρ g w)
      rw [hT,hCinv,hBinv,hT] }
  obtain ⟨c,hc⟩ := (isAbsolutelyIrreducible_iff_surjective ρ).mp inferInstance f
  refine ⟨c,?_⟩
  ext v w
  have hf : T v=c•v := (congrArg (fun f:ρ.End=>f v) hc).symm
  change C v w=c•B v w
  rw [←hT,hf]
  simp only [map_smul,LinearMap.smul_apply]

private def matrixHom (τ : Representation F G (Fin 2→F)) :
    G→*Matrix (Fin 2) (Fin 2) F := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp τ

private theorem matrixHom_det [Group.IsPerfect G]
    (τ : Representation F G (Fin 2→F)) (g:G) : (matrixHom τ g).det=1 := by
  let d := (Matrix.detMonoidHom.comp (matrixHom τ)).toHomUnits
  let : Group.IsPerfect d.range := Group.IsPerfect.range d
  exact congrArg (fun z:d.range=>(z.val:F)) (Subsingleton.elim (d.rangeRestrict g) 1)

private theorem matrixHom_mulVec (τ : Representation F G (Fin 2→F)) (g:G) (v:Fin 2→F) :
    (matrixHom τ g).mulVec v=τ g v := by
  exact congrArg (fun f:Module.End F (Fin 2→F)=>f v)
    (LinearMap.toMatrixAlgEquiv'.symm_apply_apply (τ g))

private def tensorCoordinates : ((Fin 2→F)⊗[F](Fin 2→F))≃ₗ[F]Matrix (Fin 2) (Fin 2) F :=
  (_root_.TensorProduct.comm F (Fin 2→F) (Fin 2→F)).trans
    (TensorProduct.piScalarRight F F (Fin 2→F) (Fin 2))

private theorem tensorCoordinates_tmul (x y:Fin 2→F) :
    tensorCoordinates (x⊗ₜ[F]y)=Matrix.vecMulVec x y := by
  ext i j
  change (TensorProduct.piScalarRight F F (Fin 2→F) (Fin 2)) (y⊗ₜ[F]x) i j=_
  rw [TensorProduct.piScalarRight_apply,TensorProduct.piScalarRightHom_tmul]
  rfl

private theorem tensorCoordinates_action
    (τ : Representation F G (Fin 2→F)) (σ : Representation F H (Fin 2→F))
    (g:G×H) (x:(Fin 2→F)⊗[F](Fin 2→F)) :
    tensorCoordinates (externalTensor τ σ g x)=
      matrixHom τ g.1 * tensorCoordinates x * (matrixHom σ g.2).transpose := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy,mul_add,add_mul]
  | tmul x y =>
    change tensorCoordinates (τ g.1 x⊗ₜ[F]σ g.2 y)=_
    rw [tensorCoordinates_tmul,tensorCoordinates_tmul,Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul,Matrix.vecMul_transpose,matrixHom_mulVec,matrixHom_mulVec]

/-- An irreducible degree-four action of two nontrivial perfect factors
preserves a genuine quadratic form with any prescribed nondegenerate
invariant polar form. The tensor coordinates are constructed in the proof. -/
theorem exists_compatible_quadratic [Finite F] [Group.IsPerfect G] [Group.IsPerfect H]
    (ρ : Representation F (G×H) V) [ρ.IsIrreducible]
    (hl : ρ.comp (MonoidHom.inl G H)≠1)
    (hr : ρ.comp (MonoidHom.inr G H)≠1) (hdim : Module.finrank F V=4)
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (hBinv : ∀g v w,B (ρ g v) (ρ g w)=B v w) :
    ∃Q:QuadraticForm F V,Q.polarBilin=B ∧ ∀g v,Q (ρ g v)=Q v := by
  let : ρ.IsAbsolutelyIrreducible := absolute_of_perfect_product_degree_four ρ hl hr hdim
  obtain ⟨τ,σ,⟨eT⟩⟩ := exists_two_tensor ρ hl hr hdim
  let e := eT.toLinearEquiv.trans (tensorCoordinates (F:=F))
  let Q₀ : QuadraticForm F V := ClassicalOrthogonal.FourPlusMatrix.determinantForm.comp e.toLinearMap
  have hact (g:G×H) (v:V) :
      e (ρ g v)=matrixHom τ g.1*e v*(matrixHom σ g.2).transpose := by
    change tensorCoordinates (eT (ρ g v))=_
    have he : eT (ρ g v)=externalTensor τ σ g (eT v) := Representation.IntertwiningMap.isIntertwining ρ (externalTensor τ σ) eT.toIntertwiningMap g v
    rw [he]
    exact tensorCoordinates_action τ σ g (eT v)
  have hQ₀ (g:G×H) (v:V) : Q₀ (ρ g v)=Q₀ v := by
    change ClassicalOrthogonal.FourPlusMatrix.determinantForm (e (ρ g v))=
      ClassicalOrthogonal.FourPlusMatrix.determinantForm (e v)
    rw [ClassicalOrthogonal.FourPlusMatrix.determinantForm_apply,
      ClassicalOrthogonal.FourPlusMatrix.determinantForm_apply,hact,
      Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,matrixHom_det,matrixHom_det,
      one_mul,mul_one]
  have hCinv (g:G×H) (v w:V) : Q₀.polarBilin (ρ g v) (ρ g w)=Q₀.polarBilin v w := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←map_add,hQ₀]
  obtain ⟨c,hc⟩ := invariant_form_scalar ρ B hB hBinv Q₀.polarBilin hCinv
  have hc0 : c≠0 := by
    intro hz
    have h := LinearMap.congr_fun (LinearMap.congr_fun hc
      (e.symm !![1,0;0,0])) (e.symm !![0,0;0,1])
    simp only [hz,zero_smul,LinearMap.zero_apply] at h
    have hval : Q₀.polarBilin (e.symm !![1,0;0,0]) (e.symm !![0,0;0,1])=1 := by
      simp [Q₀,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
        QuadraticMap.comp_apply,ClassicalOrthogonal.FourPlusMatrix.determinantForm_apply,
        Matrix.det_fin_two]
    exact one_ne_zero (hval.symm.trans h)
  refine ⟨c⁻¹•Q₀,?_,?_⟩
  · ext v w
    change c⁻¹*Q₀ (v+w)-c⁻¹*Q₀ v-c⁻¹*Q₀ w=B v w
    have hh := LinearMap.congr_fun (LinearMap.congr_fun hc v) w
    change Q₀ (v+w)-Q₀ v-Q₀ w=c*B v w at hh
    calc
      _ = c⁻¹*(Q₀ (v+w)-Q₀ v-Q₀ w) := by ring
      _ = B v w := by rw [hh,←mul_assoc,inv_mul_cancel₀ hc0,one_mul]
  · intro g v
    change c⁻¹*Q₀ (ρ g v)=c⁻¹*Q₀ v
    rw [hQ₀]
end Representation.ComponentTensor
