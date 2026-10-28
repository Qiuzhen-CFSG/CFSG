module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.Dual
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.Inputs
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange
public import Theory.Representation.FactorDegreeFiltration.FiniteDual

/-!
# Forty-four coordinates for the native exterior sections

A basis transports the contraction kernel and its dual to the fixed coordinate
space. The explicit equivalences preserve the M24 marking and the native
exterior-section maps. Scalar extension commutes with duality, so absolute
irreducibility of the kernel implies absolute irreducibility of both models.
Inequivalence remains an explicit, separate premise.

Source context: James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; GM02, Proposition 5.1, manuscript p.17.
-/

public section
open Sporadic.Mathieu Representation
open Representation.MathieuM24Degree44.FiveSpace
noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour

private def coordinateEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M24 V) (E : V ≃ₗ[ZMod 2] (Fin 44 → ZMod 2)) :
    ρ.Equiv (E.conjRingEquiv.toMonoidHom.comp ρ) :=
  .mk E (by
    intro g
    apply LinearMap.ext
    intro v
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [LinearEquiv.symm_apply_apply])

@[expose] def kernelCoordinates : Kernel ≃ₗ[ZMod 2] (Fin 44 → ZMod 2) :=
  (Module.finBasisOfFinrankEq (ZMod 2) Kernel finrank_kernel).equivFun

@[expose] def dualKernelCoordinates : DualKernel ≃ₗ[ZMod 2] (Fin 44 → ZMod 2) :=
  (Module.finBasisOfFinrankEq (ZMod 2) DualKernel finrank_dualKernel).equivFun

/-- The native code exterior kernel transported to 44 coordinates. -/
@[expose] def codeModel : Representation (ZMod 2) M24 (Fin 44 → ZMod 2) :=
  kernelCoordinates.conjRingEquiv.toMonoidHom.comp kernelRepresentation

/-- The dual kernel, a native cocode exterior quotient, in 44 coordinates. -/
@[expose] def cocodeModel : Representation (ZMod 2) M24 (Fin 44 → ZMod 2) :=
  dualKernelCoordinates.conjRingEquiv.toMonoidHom.comp dualKernelRepresentation

def codeModelEquiv : kernelRepresentation.Equiv codeModel :=
  coordinateEquiv kernelRepresentation kernelCoordinates

def cocodeModelEquiv : dualKernelRepresentation.Equiv cocodeModel :=
  coordinateEquiv dualKernelRepresentation dualKernelCoordinates

/-- The actual map from the invariant code exterior kernel to its coordinate model. -/
def codeModelSectionMap : kernel.toRepresentation.IntertwiningMap codeModel :=
  codeModelEquiv.toIntertwiningMap

theorem codeModelSectionMap_surjective : Function.Surjective codeModelSectionMap :=
  codeModelEquiv.toLinearEquiv.surjective

/-- The actual surjection from the full cocode exterior square to its coordinate model. -/
def cocodeModelSectionMap :
    (⊤ : Subrepresentation cocodeExterior).toRepresentation.IntertwiningMap cocodeModel :=
  cocodeModelEquiv.toIntertwiningMap.comp dualKernelSectionMap

theorem cocodeModelSectionMap_surjective : Function.Surjective cocodeModelSectionMap :=
  cocodeModelEquiv.toLinearEquiv.surjective.comp dualKernelSectionMap_surjective

theorem codeModel_isSectionOf : IsSectionOf codeModel codeExterior :=
  ⟨kernel, codeModelSectionMap, codeModelSectionMap_surjective⟩

theorem cocodeModel_isSectionOf : IsSectionOf cocodeModel cocodeExterior :=
  ⟨⊤, cocodeModelSectionMap, cocodeModelSectionMap_surjective⟩

/-- Finite-dimensional duality and scalar extension preserve absolute simplicity. -/
theorem dualKernel_absolute (h : IsAbsolutelyIrreducible kernelRepresentation) :
    IsAbsolutelyIrreducible dualKernelRepresentation := by
  let : IsIrreducible (extendScalars (AlgebraicClosure (ZMod 2)) kernelRepresentation) :=
    h.irreducible_of_closure
  refine ⟨?_⟩
  exact (RepEquiv.ofRepresentationEquiv
    (BinaryFieldDescent.dualBaseChange (K := AlgebraicClosure (ZMod 2))
      kernelRepresentation)).irreducible_euqiv.mpr isIrreducible_dual

private theorem absolute_of_equiv {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) M24 V} {σ : Representation (ZMod 2) M24 W}
    (e : ρ.Equiv σ) (h : IsAbsolutelyIrreducible ρ) : IsAbsolutelyIrreducible σ := by
  exact ⟨(RepEquiv.ofRepresentationEquiv
    (BinaryFieldDescent.extendEquiv (K := AlgebraicClosure (ZMod 2)) e)).irreducible_euqiv.mp
      h.irreducible_of_closure⟩

theorem codeModel_absolute (h : IsAbsolutelyIrreducible kernelRepresentation) :
    IsAbsolutelyIrreducible codeModel := absolute_of_equiv codeModelEquiv h

theorem cocodeModel_absolute (h : IsAbsolutelyIrreducible kernelRepresentation) :
    IsAbsolutelyIrreducible cocodeModel :=
  absolute_of_equiv cocodeModelEquiv (dualKernel_absolute h)

theorem codeModel_cocodeModel_inequivalent
    (h : IsEmpty (kernelRepresentation.Equiv dualKernelRepresentation)) :
    IsEmpty (codeModel.Equiv cocodeModel) :=
  ⟨fun e => h.false ((codeModelEquiv.trans e).trans cocodeModelEquiv.symm)⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
