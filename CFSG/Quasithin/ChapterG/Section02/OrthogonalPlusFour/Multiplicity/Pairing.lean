module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# The final dimension step for a commutator-pairing route

A nondegenerate scalar pairing between the two actual factor summands
identifies each with the dual of the other. Their dimensions, and hence
their natural-module multiplicities, agree. This module only supplies the
final dimension step: constructing the pairing from the source groups is
a separate obligation. The residual-factor consumer is included explicitly.

Source: the common-multiplicity clause of Aschbacher–Smith G.2.6(5),
printed p.336/PDF p.347.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
variable [((S₂ D g).subgroupOf (D.S g)).Normal]
  [IsElementaryAbelian 2 (Quotient D g)]
variable {d : Hypothesis D g}

/-- A pairing with zero left and right radicals forces a common multiplicity. -/
theorem SourceModuleData.common_of_pairing (f : SourceModuleData d)
    (b : f.decomposition.left.toSubmodule →ₗ[ZMod 2]
      f.decomposition.right.toSubmodule →ₗ[ZMod 2] ZMod 2)
    (hl : Function.Injective b) (hr : Function.Injective b.flip) :
    f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity := by
  let := LinearMap.IsPerfPair.of_injective hl hr
  exact f.commonMultiplicity_iff_finrank.mpr (Module.finrank_of_isPerfPair b)

/-- The pairing route discharges the multiplicity premise of the actual
residual-factor module conclusion, with all quotient coordinates preserved. -/
def SourceModuleData.factorConclusion_of_pairing (f : SourceModuleData d)
    (b : f.decomposition.left.toSubmodule →ₗ[ZMod 2]
      f.decomposition.right.toSubmodule →ₗ[ZMod 2] ZMod 2)
    (hl : Function.Injective b) (hr : Function.Injective b.flip) :
    Chapter15Collapse.FactorModuleConclusion (D.I g) (D.S g) (S₂ D g) D.L
      (moduleProjection d.quotientSymmetricEquiv) f.representation :=
  f.factorConclusion (f.common_of_pairing b hl hr)

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
