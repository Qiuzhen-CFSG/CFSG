module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.ExternalTensor
public import Theory.Representation.ExtendScalars
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Scalar comparisons for natural external tensors

Scalar extension of the natural action is entrywise extension of its matrices.
The standard tensor base-change map intertwines the external tensor actions.
A common-field isomorphism acts on both tensor coordinates semilinearly and
therefore gives a binary linear intertwiner after restricting scalars.

These actual equivalences supply the comparison maps for Noether--Deuring
descent in GLS2, Theorem 25.14, Step 5 and the statement's remarks
(`refs/KGroup/GLS2/ChapterG.tex`, lines 786--788 and 906--928).
-/

public noncomputable section

open scoped MatrixGroups TensorProduct
namespace Representation.QuadraticFourGroup.TensorClassification

variable {n : ℕ} {E F : Type*} [Field E] [Field F]

/-- Scalar extension is entrywise extension of the natural matrices. -/
def naturalActionBaseChange [Algebra E F] (e : GaloisField 2 n →+* E) :
    (extendScalars F (naturalAction e)).Equiv
      (naturalAction ((algebraMap E F).comp e)) := by
  refine Representation.Equiv.mk (TensorProduct.piScalarRight E F F (Fin 2)) (fun g => ?_)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a v =>
    ext i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, extendScalars_apply,
      LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    simp only [Algebra.smul_def]
    change algebraMap E F
      (Matrix.mulVec (((specialLinearEquivFactor n).symm g).val.map e) v i) * a =
        Matrix.mulVec (((specialLinearEquivFactor n).symm g).val.map
          ((algebraMap E F).comp e)) (fun j => algebraMap E F (v j) * a) i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, RingHom.comp_apply,
      Matrix.map_apply, Finset.sum_mul, mul_assoc]

/-- Scalar extension distributes over an external tensor, retaining the actions. -/
def externalTensorBaseChange {G H U W : Type*} [Monoid G] [Monoid H]
    [AddCommGroup U] [Module E U] [AddCommGroup W] [Module E W] [Algebra E F]
    (ρ : Representation E G U) (τ : Representation E H W) :
    (extendScalars F (externalTensor ρ τ)).Equiv
      (externalTensor (extendScalars F ρ) (extendScalars F τ)) :=
  .mk (TensorProduct.AlgebraTensorModule.distribBaseChange E F U W) (by
    intro g
    ext u w
    rfl)

/-- Simultaneous coefficient extension of both natural factors. -/
def naturalTensorBaseChange [Algebra E F] (e₁ e₂ : GaloisField 2 n →+* E) :
    (extendScalars F (externalTensor (naturalAction e₁) (naturalAction e₂))).Equiv
      (externalTensor (naturalAction ((algebraMap E F).comp e₁))
        (naturalAction ((algebraMap E F).comp e₂))) :=
  (externalTensorBaseChange (naturalAction e₁) (naturalAction e₂)).trans
    (externalTensorEquiv (naturalActionBaseChange e₁) (naturalActionBaseChange e₂))

local instance (f : E ≃+* F) : RingHomInvPair f.toRingHom f.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv f

local instance (f : E ≃+* F) : RingHomInvPair f.symm.toRingHom f.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm f

private def coordinateFieldEquiv (f : E ≃+* F) :
    (Fin 2 → E) ≃ₛₗ[f.toRingHom] (Fin 2 → F) where
  toFun v := fun i => f (v i)
  invFun v := fun i => f.symm (v i)
  left_inv v := by ext i; exact f.symm_apply_apply _
  right_inv v := by ext i; exact f.apply_symm_apply _
  map_add' v w := by ext i; exact map_add f _ _
  map_smul' a v := by ext i; exact map_mul f _ _

private theorem coordinateFieldEquiv_intertwines (f : E ≃+* F)
    (e : GaloisField 2 n →+* E) (g : Factor n) (v : Fin 2 → E) :
    coordinateFieldEquiv f (naturalAction e g v) =
      naturalAction (f.toRingHom.comp e) g (coordinateFieldEquiv f v) := by
  ext i
  change f (Matrix.mulVec (((specialLinearEquivFactor n).symm g).val.map e) v i) =
    Matrix.mulVec (((specialLinearEquivFactor n).symm g).val.map (f.toRingHom.comp e))
      (fun j => f (v j)) i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]

/-- Changing the common coefficient field gives an actual binary tensor intertwiner. -/
def naturalTensorFieldEquiv [Algebra (ZMod 2) E] [Algebra (ZMod 2) F]
    (f : E ≃+* F) (e₁ e₂ : GaloisField 2 n →+* E) :
    (restrictScalars (k := ZMod 2) (externalTensor (naturalAction e₁) (naturalAction e₂))).Equiv
      (restrictScalars (k := ZMod 2)
        (externalTensor (naturalAction (f.toRingHom.comp e₁))
          (naturalAction (f.toRingHom.comp e₂)))) := by
  let c := TensorProduct.congr (coordinateFieldEquiv f) (coordinateFieldEquiv f)
  let b := LinearEquiv.ofBijective (c.toAddEquiv.toAddMonoidHom.toZModLinearMap 2) c.bijective
  refine Representation.Equiv.mk b (fun g => ?_)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul v w =>
    change c ((naturalAction e₁ g.1 v) ⊗ₜ[E] (naturalAction e₂ g.2 w)) =
      TensorProduct.map (naturalAction (f.toRingHom.comp e₁) g.1)
        (naturalAction (f.toRingHom.comp e₂) g.2) (c (v ⊗ₜ[E] w))
    simp only [c, TensorProduct.congr_tmul, TensorProduct.map_tmul,
      coordinateFieldEquiv_intertwines]

end Representation.QuadraticFourGroup.TensorClassification
