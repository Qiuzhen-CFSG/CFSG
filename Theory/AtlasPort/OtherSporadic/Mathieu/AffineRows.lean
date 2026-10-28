/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeAutomorphismPackage
public import Theory.AtlasPort.OtherSporadic.Codes.GolayRecovery

/-!
# AffineRows

The four rows of a Golay tetrad are identified with the Kleinian alphabet. Every row
permutation has a unique affine expression, and the polar and quadratic letter formulas
give the row form of the Golay encoder.

Source: `Atlas/Mathieu/AffineRows.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

/-- The fixed row labels 0,a,b,c in the existing binary lift. -/
def rowLabel : Fin 4 ≃ K where
  toFun k := ![0,a,b,c] k
  invFun u := if u = 0 then 0 else if u = a then 1 else if u = b then 2 else 3
  left_inv := by decide
  right_inv := by decide

theorem rowLabel_table : (rowLabel 0,rowLabel 1,rowLabel 2,rowLabel 3) = (0,a,b,c) := rfl

theorem letter_self_add : ∀ u : K, u+u = 0 := by decide

theorem j_row_polar : ∀ (u : K) (k : Fin 4), j u k = polar u (rowLabel k) := by decide

def lastColumnBit (i : HexIndex) : Bit := if i = (2,1) then 1 else 0

theorem eta_row_quadratic : ∀ (i : HexIndex) (k : Fin 4),
    eta (i,k) = 1 + qK (rowLabel k) + lastColumnBit i := by decide

/-- Every four-point permutation has a unique affine normal form. -/
def rowLinearPart (e : Equiv.Perm K) : KIsometry :=
  zeroFixingLinear (e.trans (Equiv.addRight (-e 0))) (by simp)

theorem row_affine_formula (e : Equiv.Perm K) (z : K) : rowLinearPart e z + e 0 = e z := by
  change (e z + -e 0) + e 0 = e z
  simp

theorem row_affine_unique (e : Equiv.Perm K) (L : KIsometry) (t : K)
    (h : ∀ z, e z = L z + t) : t = e 0 ∧ L = rowLinearPart e := by
  have ht : t = e 0 := by simpa using (h 0).symm
  refine ⟨ht,?_⟩
  apply LinearEquiv.ext
  intro z
  apply add_right_cancel (b := e 0)
  rw [row_affine_formula,← ht,← h]

/-- Pullback of a word written in affine row coordinates, with arbitrary ambient parameters. -/
def rowEncoder (h : HexWord) (r : HexIndex → Bit) (ε : Bit) : BinaryWord :=
  fun p => polar (h p.1) (rowLabel p.2) + r p.1 +
    ε * (1 + qK (rowLabel p.2) + lastColumnBit p.1)

theorem rowEncoder_lift (h : HexWord) (r : Fin 6 → Bit) (ε : Bit) :
    rowEncoder h (fun i => r (hexIndexEquiv i)) ε = jWord h + rho r + ε • eta := by
  funext p
  simp only [rowEncoder,Pi.add_apply,Pi.smul_apply,jWord,rho,
    LinearMap.coe_mk,AddHom.coe_mk,smul_eq_mul]
  rw [j_row_polar,eta_row_quadratic]

theorem rowEncoder_golayEquiv (h : hexacode) (r : P6) (ε : Bit) :
    rowEncoder h.val (fun i => r.val (hexIndexEquiv i)) ε = (golayEquiv (h,r,ε) : BinaryWord) := by
  rw [rowEncoder_lift,golayEquiv_apply]

end Atlas.Codes
