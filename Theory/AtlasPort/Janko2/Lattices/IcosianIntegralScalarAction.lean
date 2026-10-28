/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianIntegralScalarAction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianIntegralComparison
public import Theory.AtlasPort.Janko2.Lattices.IcosianAxisRoots
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Icosian Integral Scalar Action

The opposite icosian order acts faithfully by integral endomorphisms
of the lattice and, through the proved comparison, of the Leech lattice.
Evaluation on a doubled axis vector proves faithfulness.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianIntegralScalarAction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

/-- Every integral right scalar acts on the actual congruence lattice. The
opposite ring records the order of composition of right multiplications. -/
def icosianIntegralRightScalars : icosianOrderᵐᵒᵖ →+* Module.End ℤ IcosianLattice :=
  Module.toModuleEnd ℤ IcosianLattice

/-- Transport of all integral right scalars through the proved integral
comparison onto the retained Golay Leech lattice. No isometry claim is made for
arbitrary scalars. -/
def icosianLeechRightScalars : icosianOrderᵐᵒᵖ →+* Module.End ℤ leech :=
  icosianLeechEquiv.conjRingEquiv.toRingHom.comp icosianIntegralRightScalars

theorem icosianIntegralRightScalars_apply (a : icosianOrderᵐᵒᵖ)
    (x : IcosianLattice) (i : Fin 3) :
    (icosianIntegralRightScalars a x).val i=x.val i*MulOpposite.unop a := rfl

theorem icosianLeechRightScalars_comparison (a : icosianOrderᵐᵒᵖ) (x : IcosianLattice) :
    icosianLeechRightScalars a (icosianLeechEquiv x)=
      icosianLeechEquiv (icosianIntegralRightScalars a x) := by
  change icosianLeechEquiv (icosianIntegralRightScalars a
    (icosianLeechEquiv.symm (icosianLeechEquiv x)))=_
  rw [icosianLeechEquiv.symm_apply_apply]

theorem icosianLeechRightScalars_rational (a : icosianOrderᵐᵒᵖ) (x : IcosianLattice) :
    rationalEmbedding (icosianLeechRightScalars a (icosianLeechEquiv x)).val=
      icosianComparison (fun i => (x.val i).val*(MulOpposite.unop a).val) := by
  rw [icosianLeechRightScalars_comparison,icosianLeechEquiv_agrees]
  rfl

theorem icosianIntegralRightScalars_injective : Function.Injective icosianIntegralRightScalars := by
  intro a b h
  let x : IcosianLattice := ⟨(icosianAxisRoot (0,1)).val,(icosianAxisRoot (0,1)).property.1⟩
  have he := congrArg (fun f : Module.End ℤ IcosianLattice => (f x).val 0) h
  rw [icosianIntegralRightScalars_apply,icosianIntegralRightScalars_apply] at he
  have hx : x.val 0=(2 : icosianOrder) := by
    apply Subtype.ext
    change (2 : IcosianQuaternion)*1=2
    exact mul_one _
  rw [hx] at he
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have he' := congrArg Subtype.val he
  change (2 : IcosianQuaternion)*(MulOpposite.unop a).val=
    2*(MulOpposite.unop b).val at he'
  rw [two_mul,two_mul] at he'
  have hhalf := congrArg (fun z : IcosianQuaternion => (1/2 : ℚ) • z) he'
  simpa [smul_add,← add_smul] using hhalf

theorem icosianLeechRightScalars_injective : Function.Injective icosianLeechRightScalars :=
  icosianLeechEquiv.conjRingEquiv.injective.comp icosianIntegralRightScalars_injective

end Atlas.Lattices
