module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/Basic.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.Algebra.SplitOctonion.Automorphism
public import Mathlib.LinearAlgebra.Dimension.Constructions
set_option warningAsError false

@[expose] public section

/-! The actual full split-octonion automorphism model; no order or simplicity assumptions. -/
namespace Atlas.G2
variable (F : Type*) [Field F]

abbrev Model := Atlas.SplitOctonion.Automorphism F

instance [Finite F] : Finite (Model F) :=
  Finite.of_injective (fun g : Model F => (g.val : Atlas.SplitOctonion.Carrier F →
    Atlas.SplitOctonion.Carrier F)) (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

/-- The defining eight-dimensional faithful linear representation. -/
def representation : Model F →* (Atlas.SplitOctonion.Carrier F ≃ₗ[F]
    Atlas.SplitOctonion.Carrier F) :=
  Atlas.Algebra.MultiplicativeLinearAut.representation

theorem representation_injective : Function.Injective (representation F) :=
  Atlas.Algebra.MultiplicativeLinearAut.representation_injective

theorem carrier_finrank : Module.finrank F (Atlas.SplitOctonion.Carrier F) = 8 := by
  simp [Atlas.SplitOctonion.Carrier]
theorem finite_model [Finite F] : Finite (Model F) := inferInstance
end Atlas.G2
