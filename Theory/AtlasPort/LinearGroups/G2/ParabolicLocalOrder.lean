module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Uses the root coordinates of the existing CFSG ATLAS port, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: injectivity of the short-parabolic Borel cells and exact local order.
-/

public import Theory.AtlasPort.LinearGroups.G2.LieParabolicCells
/-!
# The short G₂ parabolic has q+1 Borel cosets

The two-cell decomposition already bounds the order above. Applying an equality
of cell representatives to the first singular vector distinguishes the missing
point from every affine parameter and then recovers that parameter. Cancellation
recovers the Borel factor, making the parametrization injective as well.

This supplies the exact endpoint order and local valence used in the ternary
completion path argument of Aschbacher–Smith F.4.6, printed pp.276–277.
-/

open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
@[expose] public noncomputable section
namespace Atlas.G2.ParabolicCells
variable {F : Type*} [Field F]
private def shortRepresentative : Option F → Model F
  | none => 1
  | some a => rootF a * weylS
private theorem shortRepresentative_mem (a : Option F) : shortRepresentative a ∈ parabolic₁ := by
  cases a with
  | none => exact one_mem _
  | some a =>
      exact parabolic₁.mul_mem
        (borel_le_parabolic₁ (mem_sup_left (subset_closure (by simp))))
        (mem_sup_right (subset_closure (by simp)))
private def shortCellMap : Option F × borel (K := F) → parabolic₁ (F := F) :=
  fun p => ⟨shortRepresentative p.1 * p.2.val,
    parabolic₁.mul_mem (shortRepresentative_mem p.1) (borel_le_parabolic₁ p.2.property)⟩
private theorem shortCellMap_injective : Function.Injective (shortCellMap (F := F)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  have he' : shortRepresentative a * b.val = shortRepresentative c * d.val := congrArg Subtype.val he
  obtain ⟨u,hu⟩ := (mem_pointStabilizer_iff b.val).mp
    (parabolic_le_pointStabilizer (borel_le_parabolic₂ b.property))
  obtain ⟨v,hv⟩ := (mem_pointStabilizer_iff d.val).mp
    (parabolic_le_pointStabilizer (borel_le_parabolic₂ d.property))
  have hvec := congrArg (fun g : Model F => g.val (basisVector 0)) he'
  change (shortRepresentative a).val (b.val.val (basisVector 0)) =
    (shortRepresentative c).val (d.val.val (basisVector 0)) at hvec
  rw [hu,hv] at hvec
  have h0 := congrFun hvec 0
  have h1 := congrFun hvec 1
  have hac : a=c := by
    cases a with
    | none =>
      cases c with
      | none => rfl
      | some c =>
        simp [shortRepresentative,Units.smul_def,basisVector,
          weylS,weylSEquiv,weylSLinear,weylSApply,rootF,rootFEquiv,rootFLinear,rootFApply] at h1
    | some a =>
      cases c with
      | none =>
        simp [shortRepresentative,Units.smul_def,basisVector,
          weylS,weylSEquiv,weylSLinear,weylSApply,rootF,rootFEquiv,rootFLinear,rootFApply] at h1
      | some c =>
        simp [shortRepresentative,Units.smul_def,basisVector,
          weylS,weylSEquiv,weylSLinear,weylSApply,rootF,rootFEquiv,rootFLinear,rootFApply] at h0 h1
        have huv : (u : F) = v := h1
        rw [huv] at h0
        exact congrArg some (mul_left_cancel₀ v.ne_zero h0)
  subst c
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel he'))

/-- Exact size of the short endpoint, with the whole Borel as its flag stabilizer. -/
theorem short_card [Finite F] : Nat.card (parabolic₁ (F := F)) =
    (Nat.card F + 1) * Nat.card (borel (K := F)) := by
  apply le_antisymm short_card_le
  simpa only [Nat.card_prod,Finite.card_option] using
    Nat.card_le_card_of_injective (shortCellMap (F := F)) shortCellMap_injective
end Atlas.G2.ParabolicCells
