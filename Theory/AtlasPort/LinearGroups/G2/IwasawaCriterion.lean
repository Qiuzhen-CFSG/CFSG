module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/IwasawaCriterion.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.LocalNormalizer
public import Theory.AtlasPort.GroupTheory.G2IwasawaStabilizer

/-! The faithful primitive singular action and abelian long-root local subgroup imply simplicity by the stabilizer Iwasawa criterion. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

instance model_nontrivial : Nontrivial (Model F) := by
  refine ⟨⟨rootA 0,rootA 1,?_⟩⟩
  exact fun h => zero_ne_one (rootA_injective h)

/-- The concrete singular action and its two-dimensional long-root local subgroup
satisfy the Iwasawa criterion as soon as primitivity has been established. -/
theorem isSimple_of_preprimitive [Finite F] (hq : 2 < Nat.card F)
    [MulAction.IsPreprimitive (Model F) (SingularPoints F)] : IsSimpleGroup (Model F) := by
  let := isPerfect hq
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple firstPoint longRootLocal
    longRootLocal_le_pointStabilizer longRootLocal_normal_in_pointStabilizer
    longRootLocal_commutative (longRootNormalClosure_eq_top hq)
end Atlas.G2
