module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.KernelGeneration
public import Mathlib.Algebra.Group.Equiv.Finite
/-!
# The actual universal kernel modulo squares

The proved exceptional multiplier gives a canonical binary-plane quotient whose kernel
is exactly the subgroup of squares. Unique universal lifting induces an actual
automorphism action on this quotient. A checked four-element calculation proves
that an involution commuting with a nonidentity cubic action is the identity.

Source: Aschbacher–Smith I.2.2(3b), printed pp.409–410, and I.1.3(6), p.407.
-/

public section
open PerfectCentralCovering Subgroup
namespace Matrix.PSL3Four.CentralCover.GraphFieldKernel
open ExtendedCentralizer.CoverCentralizers.DiagonalCenter
noncomputable section
abbrev Kernel := (universalProjection PSL).ker

@[expose] def binaryProjection : Kernel →* BinaryKernelPlane :=
  multiplierBinaryCoordinates.comp PSL3.ExceptionalFourCover.canonicalKernelEquiv.toMonoidHom

theorem binaryProjection_surjective : Function.Surjective binaryProjection :=
  multiplierBinaryCoordinates_surjective.comp PSL3.ExceptionalFourCover.canonicalKernelEquiv.surjective

theorem binaryProjection_eq_one_iff_square (z : Kernel) :
    binaryProjection z = 1 ↔ ∃ w : Kernel, w^2=z := by
  constructor
  · intro hz
    obtain ⟨y,hy⟩ := (multiplierBinaryCoordinates_eq_one_iff_square
      (PSL3.ExceptionalFourCover.canonicalKernelEquiv z)).mp hz
    refine ⟨PSL3.ExceptionalFourCover.canonicalKernelEquiv.symm y,
      PSL3.ExceptionalFourCover.canonicalKernelEquiv.injective ?_⟩
    simpa only [map_pow,MulEquiv.apply_symm_apply] using hy
  · rintro ⟨w,rfl⟩
    rw [map_pow]
    exact (by decide +kernel : ∀ v : BinaryKernelPlane,v^2=1) _

@[expose] def binaryMap (β : MulAut PSL) : BinaryKernelPlane →* BinaryKernelPlane :=
  binaryProjection.liftOfSurjective binaryProjection_surjective
    ⟨binaryProjection.comp (universalKernelMap β),by
      intro z hz
      obtain ⟨w,rfl⟩ := (binaryProjection_eq_one_iff_square z).mp hz
      change binaryProjection (universalKernelMap β (w^2))=1
      rw [map_pow,map_pow]
      exact (by decide +kernel : ∀ v : BinaryKernelPlane,v^2=1) _⟩

theorem binaryMap_apply (β : MulAut PSL) (z : Kernel) :
    binaryMap β (binaryProjection z) = binaryProjection (universalKernelMap β z) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z

theorem kernelMap_one (z : Kernel) : universalKernelMap 1 z=z := by
  have he : universalLift 1=1 := (universalLift_unique 1 1 (fun _ => rfl)).symm
  apply Subtype.ext
  exact congrArg (fun a : MulAut (UniversalGroup PSL) => a z) he

theorem binaryMap_one (v : BinaryKernelPlane) : binaryMap 1 v=v := by
  obtain ⟨z,rfl⟩ := binaryProjection_surjective v
  rw [binaryMap_apply,kernelMap_one]

theorem binaryMap_mul (β γ : MulAut PSL) (v : BinaryKernelPlane) :
    binaryMap (β*γ) v=binaryMap β (binaryMap γ v) := by
  obtain ⟨z,rfl⟩ := binaryProjection_surjective v
  rw [binaryMap_apply,binaryMap_apply,binaryMap_apply,universalKernelMap_mul]

@[expose] def binaryAction (β : MulAut PSL) : MulAut BinaryKernelPlane :=
 { binaryMap β with
   invFun := binaryMap β⁻¹
   left_inv v := by
     change binaryMap β⁻¹ (binaryMap β v)=v
     rw [←binaryMap_mul,inv_mul_cancel,binaryMap_one]
   right_inv v := by
     change binaryMap β (binaryMap β⁻¹ v)=v
     rw [←binaryMap_mul,mul_inv_cancel,binaryMap_one] }

theorem binaryAction_apply (β : MulAut PSL) (z : Kernel) :
    binaryAction β (binaryProjection z)=binaryProjection (universalKernelMap β z) :=
  binaryMap_apply β z

theorem binaryAction_one : binaryAction 1=1 := by
  apply MulEquiv.ext
  intro v
  exact binaryMap_one v

theorem binaryAction_mul (β γ : MulAut PSL) :
    binaryAction (β*γ)=binaryAction β*binaryAction γ := by
  apply MulEquiv.ext
  intro v
  exact binaryMap_mul β γ v

@[expose] def binaryActionHom : MulAut PSL →* MulAut BinaryKernelPlane where
  toFun := binaryAction
  map_one' := binaryAction_one
  map_mul' := binaryAction_mul

theorem binary_involutory_centralizer : ∀ a b : MulAut BinaryKernelPlane,
    a^3=1 → a≠1 → b^2=1 → a*b=b*a → b=1 := by
  have h : ∀ a b : MulAut BinaryKernelPlane,
    (decide (a^3=1) && decide (a≠1) && decide (b^2=1) && decide (a*b=b*a) && decide (b≠1)) = false := by
    decide +kernel
  intro a b ha hna hb hc
  by_contra hn
  have hh := h a b
  simp [ha,hna,hb,hc,hn] at hh

end
end Matrix.PSL3Four.CentralCover.GraphFieldKernel
