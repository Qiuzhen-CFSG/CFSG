module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The dual kernel as a native cocode exterior quotient

The determinant pairing on exterior squares, combined with the perfect native
code--cocode pairing, surjects from the cocode exterior square onto the dual of
the code exterior square. Restricting functionals to the contraction kernel
gives a surjective intertwiner onto its dual. Thus the kernel and its dual are
literal native exterior sections of dimension 44, without a simplicity premise.

Source context: James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; GM02, Proposition 5.1, manuscript p.17.
-/

@[expose] public section
open Sporadic.Mathieu MathieuCode Representation
open Representation.MathieuM24Degree44.FiveSpace
noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour

private theorem pairingDual_surjective {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (n : ℕ) :
    Function.Surjective (exteriorPower.pairingDual F V n) := by
  classical
  let b := Module.finBasis F V
  let B := b.exteriorPower n
  apply LinearMap.range_eq_top.mp
  apply top_le_iff.mp
  rw [← B.dualBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨exteriorPower.ιMulti_family F n b.coord i, ?_⟩
  rw [← exteriorPower.ιMultiDual, ← exteriorPower.basis_coord]
  exact (congrFun B.coe_dualBasis i).symm

/-- The determinant pairing induced by the actual code--cocode duality. -/
def exteriorPairingLinear : (⋀[ZMod 2]^2 Cocode) →ₗ[ZMod 2]
    Module.Dual (ZMod 2) (⋀[ZMod 2]^2 Code) :=
  (exteriorPower.pairingDual (ZMod 2) Code 2).comp
    (exteriorPower.map 2 cocodeDuality.toLinearMap)

theorem exteriorPairingLinear_surjective : Function.Surjective exteriorPairingLinear :=
  (pairingDual_surjective 2).comp
    (exteriorPower.map_surjective cocodeDuality.toLinearEquiv.surjective)

theorem exteriorPairingLinear_wedges (v : Fin 2 → Cocode) (w : Fin 2 → Code) :
    exteriorPairingLinear (exteriorPower.ιMulti (ZMod 2) 2 v)
      (exteriorPower.ιMulti (ZMod 2) 2 w) =
      Matrix.det (Matrix.of (fun i j => codeCocodePairing (w i) (v j))) := by
  simp [exteriorPairingLinear, exteriorPower.map_apply_ιMulti]

theorem exteriorPairingLinear_wedges_equivariant (g : M24)
    (v : Fin 2 → Cocode) (w : Fin 2 → Code) :
    exteriorPairingLinear
      (exteriorPower.ιMulti (ZMod 2) 2 (cocodeRepresentation g ∘ v))
      (exteriorPower.ιMulti (ZMod 2) 2 w) =
    exteriorPairingLinear (exteriorPower.ιMulti (ZMod 2) 2 v)
      (exteriorPower.ιMulti (ZMod 2) 2 (codeRepresentation g⁻¹ ∘ w)) := by
  rw [exteriorPairingLinear_wedges, exteriorPairingLinear_wedges]
  congr 1
  ext i j
  exact LinearMap.congr_fun
    (LinearMap.congr_fun (cocodeDuality.isIntertwining' g) (v j)) (w i)

/-- The determinant pairing intertwines the native exterior actions. -/
def exteriorPairing : cocodeExterior.IntertwiningMap codeExterior.dual where
  toLinearMap := exteriorPairingLinear
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    change exteriorPairingLinear
        (exteriorPower.map 2 (cocodeRepresentation g) (exteriorPower.ιMulti (ZMod 2) 2 v))
        (exteriorPower.ιMulti (ZMod 2) 2 w) =
      exteriorPairingLinear (exteriorPower.ιMulti (ZMod 2) 2 v)
        (exteriorPower.map 2 (codeRepresentation g⁻¹) (exteriorPower.ιMulti (ZMod 2) 2 w))
    simp only [exteriorPower.map_apply_ιMulti]
    exact exteriorPairingLinear_wedges_equivariant g v w

abbrev DualKernel := Module.Dual (ZMod 2) Kernel

def dualKernelRepresentation : Representation (ZMod 2) M24 DualKernel :=
  kernelRepresentation.dual

/-- Restriction of the determinant pairing to the actual contraction kernel. -/
def dualKernelMap : cocodeExterior.IntertwiningMap dualKernelRepresentation where
  toLinearMap := kernel.toSubmodule.dualRestrict.comp exteriorPairingLinear
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact LinearMap.congr_fun
      (LinearMap.congr_fun (exteriorPairing.isIntertwining' g) v) w.val

theorem dualKernelMap_surjective : Function.Surjective dualKernelMap :=
  (Subspace.dualRestrict_surjective (W := kernel.toSubmodule)).comp
    exteriorPairingLinear_surjective

theorem finrank_dualKernel : Module.finrank (ZMod 2) DualKernel = 44 := by
  rw [Subspace.dual_finrank_eq, finrank_kernel]

theorem kernel_isSectionOf : IsSectionOf kernelRepresentation codeExterior := by
  exact ⟨kernel, .id kernelRepresentation, Function.surjective_id⟩

/-- The quotient map, with the source written as the full invariant subspace. -/
def dualKernelSectionMap :
    (⊤ : Subrepresentation cocodeExterior).toRepresentation.IntertwiningMap
      dualKernelRepresentation where
  toLinearMap := dualKernelMap.toLinearMap.comp (⊤ : Submodule (ZMod 2) _).subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (dualKernelMap.isIntertwining' g) v.val

theorem dualKernelSectionMap_surjective : Function.Surjective dualKernelSectionMap := by
  exact dualKernelMap_surjective.comp
    (show Function.Surjective
      (fun v : (⊤ : Subrepresentation cocodeExterior).toSubmodule => v.val) from
        fun w => ⟨⟨w, Submodule.mem_top⟩, rfl⟩)

theorem dualKernel_isSectionOf : IsSectionOf dualKernelRepresentation cocodeExterior :=
  ⟨⊤, dualKernelSectionMap, dualKernelSectionMap_surjective⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
