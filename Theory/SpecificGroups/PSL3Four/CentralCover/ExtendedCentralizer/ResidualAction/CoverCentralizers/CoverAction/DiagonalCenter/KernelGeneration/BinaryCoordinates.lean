module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.UniversalKernel

/-!
# From an equivariant binary kernel model to diagonal coinvariants

The rotation `(x,y) ↦ (y,xy)` of the binary plane has invertible displacement
map. A surjective map from the actual universal kernel to this plane, whose
kernel consists of squares and which intertwines the actual lift with the
rotation, therefore proves generation by squares and lift displacements.

Reduction modulo two of `C₄ × C₄ × C₃` has precisely the required square
kernel. An abstract multiplier identification supplies this binary quotient,
but its compatibility with the diagonal action is a separate premise.
No identification or action of the exceptional multiplier is asserted here.

This is the elementary coinvariant step for Aschbacher--Smith 15.3.38,
printed pp.1136--1137, using the multiplier type in I.1.3(6), printed p.407,
manuscript of 1 March 2004.
-/

public section
open Subgroup PerfectCentralCovering
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter

/-- The binary plane carrying the diagonal kernel action modulo squares. -/
abbrev BinaryKernelPlane := C2 × C2

/-- The exceptional multiplier coordinates, without asserting a kernel identification. -/
abbrev ExceptionalMultiplierCoordinates :=
  (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) × Multiplicative (ZMod 3)

/-- Reduction of the two order-four coordinates modulo squares. -/
@[expose] def multiplierBinaryCoordinates : ExceptionalMultiplierCoordinates →* BinaryKernelPlane :=
  let reduceFour : Multiplicative (ZMod 4) →* C2 :=
    (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toMultiplicative
  (reduceFour.prodMap reduceFour).comp (MonoidHom.fst _ _)

/-- The order-three rotation of the nonzero points of the binary plane. -/
@[expose] def binaryKernelRotation : MulAut BinaryKernelPlane where
  toFun v := (v.2, v.1 * v.2)
  invFun v := (v.1 * v.2, v.1)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

theorem binaryKernelRotation_displacement (v : BinaryKernelPlane) :
    binaryKernelRotation (binaryKernelRotation v) * (binaryKernelRotation v)⁻¹ = v := by
  revert v
  decide +kernel

theorem multiplierBinaryCoordinates_surjective :
    Function.Surjective multiplierBinaryCoordinates := by decide +kernel

theorem multiplierBinaryCoordinates_eq_one_iff_square (x : ExceptionalMultiplierCoordinates) :
    multiplierBinaryCoordinates x = 1 ↔ ∃ y, y ^ 2 = x := by
  revert x
  decide +kernel

/-- The actual lifted action restricted to the universal projection kernel. -/
@[expose] noncomputable def universalKernelMap (β : MulAut PSL) :
    (universalProjection PSL).ker →* (universalProjection PSL).ker where
  toFun z := ⟨universalLift β z, by
    change universalProjection PSL (universalLift β z) = 1
    rw [universalLift_compatible, show universalProjection PSL z = 1 from z.property, map_one]⟩
  map_one' := Subtype.ext (map_one (universalLift β))
  map_mul' x y := Subtype.ext (map_mul (universalLift β) (x : UniversalGroup PSL) (y : UniversalGroup PSL))

/-- A surjective binary kernel model with square kernel and the indicated
rotation supplies generation by squares and actual lift displacements. -/
theorem kernel_generation_of_binary_coordinates (β : MulAut PSL)
    (q : (universalProjection PSL).ker →* BinaryKernelPlane)
    (hq : Function.Surjective q)
    (hsquare : ∀ z, q z = 1 → ∃ w, w ^ 2 = z)
    (hact : ∀ z, q (universalKernelMap β z) = binaryKernelRotation (q z)) :
    (universalProjection PSL).ker ≤ kernelSquaresAndDisplacements β := by
  intro z hz
  let z' : (universalProjection PSL).ker := ⟨z, hz⟩
  obtain ⟨w, hw⟩ := hq (binaryKernelRotation (q z'))
  let d := universalKernelMap β w * w⁻¹
  have hd : q d = q z' := by
    change q (universalKernelMap β w * w⁻¹) = q z'
    rw [map_mul, map_inv, hact, hw, binaryKernelRotation_displacement]
  have hv : q (z' * d⁻¹) = 1 := by rw [map_mul, map_inv, hd, mul_inv_cancel]
  obtain ⟨s, hs⟩ := hsquare _ hv
  have hsN : (s : UniversalGroup PSL) ^ 2 ∈ kernelSquaresAndDisplacements β :=
    subset_closure (Or.inl ⟨s, rfl⟩)
  have hdN : (d : UniversalGroup PSL) ∈ kernelSquaresAndDisplacements β :=
    subset_closure (Or.inr ⟨w, rfl⟩)
  have he : (s : UniversalGroup PSL) ^ 2 * (d : UniversalGroup PSL) = z := by
    have he := congrArg Subtype.val hs
    change (s : UniversalGroup PSL) ^ 2 = z * (d : UniversalGroup PSL)⁻¹ at he
    rw [he, inv_mul_cancel_right]
  exact he ▸ (kernelSquaresAndDisplacements β).mul_mem hsN hdN

/-- A multiplier isomorphism is useful only together with its proved
compatibility with the actual lifted action modulo squares. -/
theorem kernel_generation_of_equivariant_multiplier_coordinates (β : MulAut PSL)
    (e : (universalProjection PSL).ker ≃* ExceptionalMultiplierCoordinates)
    (hact : ∀ z, multiplierBinaryCoordinates (e (universalKernelMap β z)) =
      binaryKernelRotation (multiplierBinaryCoordinates (e z))) :
    (universalProjection PSL).ker ≤ kernelSquaresAndDisplacements β := by
  apply kernel_generation_of_binary_coordinates β
    (multiplierBinaryCoordinates.comp e.toMonoidHom)
    (multiplierBinaryCoordinates_surjective.comp e.surjective) _ hact
  intro z hz
  obtain ⟨y, hy⟩ := (multiplierBinaryCoordinates_eq_one_iff_square (e z)).mp hz
  refine ⟨e.symm y, e.injective ?_⟩
  simpa only [map_pow, e.apply_symm_apply] using hy

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
