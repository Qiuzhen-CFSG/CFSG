module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Mathlib.FieldTheory.Finite.GaloisField
/-!
# Separating PSL₃(4) from the binary linear models

Orders alone do not distinguish PSL₃(4) from PSL₄(2). Instead, the
actual upper-unitriangular Sylow subgroup of PSL₃(4) has center of
order four, and the binary projective models have Sylow centers of
order at most two. The two given model isomorphisms and finite-field
transport carry the same Sylow subgroup between the actual groups.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
1.1.5(3)(b), pp.501–503, as used in 15.4.20, p.1164.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels

/-- The equal-order PSL₃(4) and PSL₄(2) models are distinguished by their
Sylow centers, of orders four and at most two respectively. -/
theorem linearThreeFour_separation {Q : Type*} [Group Q] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (h34 : ClassicalGroup.IsPSL Q 3 4)
    (hbin : ClassicalGroup.IsPSL Q n 2) : False := by
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := h34
  obtain ⟨B, _, _, hB, ⟨eB⟩⟩ := hbin
  let : Fintype B := Fintype.ofFinite B
  let b : B ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hB)
  let e : PSL(3,F) ≃* PSL(n,ZMod 2) := eF.symm.trans (eB.trans (Atlas.fieldEquivPSL n b))
  let S := Matrix.PSL3.LinearThree.unipotentSylow F (n := 2) (by decide) (by simpa using hF)
  have hc : Nat.card (center S) = 4 := by
    change Nat.card (center (Matrix.PSL3.LinearThree.unipotent F)) = 4
    rw [← Nat.card_congr (centerCongr (Matrix.PSL3.LinearThree.unipotentEquiv F)).toEquiv]
    rw [← Matrix.PSL3Even.UnipotentGeometry.Z_eq_center,
      Matrix.PSL3Even.UnipotentGeometry.card_Z, hF]
  have hb := BinaryLinear.psl_sylow_center_card_le_two (by omega : 2 ≤ n)
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  rw [← BinaryLinear.sylow_center_card_congr e S, hc] at hb
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels
