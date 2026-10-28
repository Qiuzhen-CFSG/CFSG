module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelExtraspecial
public import Theory.Representation.PSL3Two.SmallModules
import all Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelSquares

/-!
# The two marked sections of the native two-central kernel

The octad translations modulo the marked involution are the natural
three-space. Displacement identifies the quotient of the whole kernel by
the translations with its dual, for the same actual quotient actor.
Both maps retain their full kernels and actual conjugation formulas.
No direct-product decomposition of the central quotient is asserted.
-/

public noncomputable section
open Subgroup Representation
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.KernelSections

/-- The original quotient action in binary special-linear coordinates. -/
def actor : centralizer2A →* BinaryLinearThree.Group :=
  (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp
    ((BinaryLinear.SmallParabolicLevi.linearGroupCongr quotientCoordinates).toMonoidHom.comp
      quotientAction)

theorem actor_apply (g : centralizer2A) (v : QuotientSpace) :
    BinaryLinearThree.W (actor g) (quotientCoordinates v) =
      quotientCoordinates (quotientAction g v) := by
  have h := congrArg (fun b : BinaryLinear.OuterCyclic.LinearGroup 3 =>
    b (quotientCoordinates v))
    ((BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply
      (BinaryLinear.SmallParabolicLevi.linearGroupCongr quotientCoordinates (quotientAction g)))
  change ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm
    (BinaryLinear.SmallParabolicLevi.linearGroupCongr quotientCoordinates (quotientAction g))).val.mulVec
      (quotientCoordinates v) = _
  simpa only [BinaryLinear.OuterCyclic.slEquivLinear_apply,
    BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply,
    LinearEquiv.symm_apply_apply] using h

theorem actor_ker : actor.ker = kernel := by
  rw [actor, MonoidHom.ker_comp_of_injective _ _
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.injective,
    MonoidHom.ker_comp_of_injective _ _
      (BinaryLinear.SmallParabolicLevi.linearGroupCongr quotientCoordinates).injective,
    quotientAction_ker]

/-- The natural section of the original translation kernel. -/
def natural : translationKernel →* Multiplicative BinaryLinearThree.Vector :=
  quotientCoordinates.toAddEquiv.toMultiplicative.toMonoidHom.comp qv

theorem natural_ker (u : translationKernel) : natural u = 1 ↔
    u.val ∈ zpowers (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A) := by
  rw [natural,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,←map_one quotientCoordinates.toAddEquiv.toMultiplicative,
    quotientCoordinates.toAddEquiv.toMultiplicative.injective.eq_iff]
  exact qv_eq_one_iff u

theorem natural_conjugation (g : centralizer2A) (u : translationKernel) :
    (natural (MulAut.conjNormal g u)).toAdd =
      BinaryLinearThree.W (actor g) (natural u).toAdd := by
  change quotientCoordinates (qv (MulAut.conjNormal g u)).toAdd =
    BinaryLinearThree.W (actor g) (quotientCoordinates (qv u).toAdd)
  rw [qv_conjugation,actor_apply]

private def pointKernel : kernel →*
    Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel markedVector :=
  (pointAction.comp kernel.subtype).codRestrict _ (fun q =>
    (Theory.LinearAlgebra.BinaryFivePointStabilizer.mem_kernel_iff markedVector _).mpr
      q.property.2)

private def dualCoordinates :
    (QuotientSpace →ₗ[ZMod 2] Theory.LinearAlgebra.BinaryFivePointStabilizer.line markedVector)
      ≃ₗ[ZMod 2] Module.Dual (ZMod 2) BinaryLinearThree.Vector :=
  LinearEquiv.arrowCongr quotientCoordinates lineCoordinates

/-- Displacement on the literal quotient by the octad translations. -/
def dual : kernel →* Multiplicative (Module.Dual (ZMod 2) BinaryLinearThree.Vector) :=
  dualCoordinates.toAddEquiv.toMultiplicative.toMonoidHom.comp
    ((Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacementEquiv markedVector).toMonoidHom.comp
      pointKernel)

theorem dual_ker (q : kernel) : dual q = 1 ↔ q.val ∈ translationKernel := by
  change dualCoordinates.toAddEquiv.toMultiplicative
    (Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacementEquiv markedVector
      (pointKernel q)) = 1 ↔ _
  rw [←map_one dualCoordinates.toAddEquiv.toMultiplicative,
    dualCoordinates.toAddEquiv.toMultiplicative.injective.eq_iff,
    ←map_one (Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacementEquiv markedVector),
    (Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacementEquiv markedVector).injective.eq_iff]
  change pointKernel q = 1 ↔ q.val ∈ translationKernel
  rw [←pointAction_ker,MonoidHom.mem_ker]
  exact Subtype.ext_iff

theorem dual_conjugation (g : centralizer2A) (q : kernel) :
    (dual (MulAut.conjNormal g q)).toAdd =
      BinaryLinearThree.W.dual (actor g) (dual q).toAdd := by
  apply LinearMap.ext
  intro v
  have he : pointKernel (MulAut.conjNormal g q) =
      MulAut.conjNormal (pointAction g) (pointKernel q) := by
    apply Subtype.ext
    change pointAction (g*q.val*g⁻¹)=pointAction g*pointAction q.val*(pointAction g)⁻¹
    rw [map_mul,map_mul,map_inv]
  simp only [dual,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacementEquiv_apply]
  change lineCoordinates
      (Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacement markedVector
        (pointKernel (MulAut.conjNormal g q)) (quotientCoordinates.symm v)) =
    lineCoordinates
      (Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacement markedVector
        (pointKernel q) (quotientCoordinates.symm (BinaryLinearThree.W (actor g)⁻¹ v)))
  rw [he,Theory.LinearAlgebra.BinaryFivePointStabilizer.kernelDisplacement_conjugation]
  congr 2
  apply quotientCoordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  have hh := actor_apply g⁻¹ (quotientCoordinates.symm v)
  rw [map_inv actor,map_inv quotientAction,LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.KernelSections
