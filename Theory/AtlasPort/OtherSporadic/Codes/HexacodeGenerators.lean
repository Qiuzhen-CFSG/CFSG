/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeSystematic

/-!
# HexacodeGenerators

Explicit monomial lifts of adjacent coordinate transpositions, together with an order-
three scalar, preserve the hexacode. It suffices to check the chosen binary basis;
coordinate calculations establish the lift squares and scalar conjugation relations.

Source: `Atlas/Codes/HexacodeGenerators.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

/-- Checking the six binary basis images suffices for the full stabilizer. -/
theorem monomial_mem_of_hexBasis (g : Monomial HexIndex)
    (hg : ∀ k, Monomial.act g (hexGenerators k) ∈ hexacode) :
    g ∈ Monomial.stabilizer hexacode := by
  have hl : ∀ w : hexacode, Monomial.act g w.val ∈ hexacode := by
    intro w
    have hh := congrArg (fun v : hexacode => Monomial.act g v.val) (hexBasis.sum_repr w)
    rw [← hh]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hexBasis_coe]
    exact hexacode.sum_mem (fun k _ => hexacode.smul_mem _ (hg k))
  have hm : hexacode.map (Monomial.act g).toLinearMap ≤ hexacode := by
    rintro _ ⟨w,hw,rfl⟩
    exact hl ⟨w,hw⟩
  have he := Submodule.eq_of_le_of_finrank_eq hm ((Monomial.act g).finrank_map_eq hexacode)
  intro w
  constructor
  · exact fun hw => hl ⟨w,hw⟩
  · intro hw
    have hh : Monomial.act g w ∈ hexacode.map (Monomial.act g).toLinearMap := by rw [he]; exact hw
    obtain ⟨v,hv,hvw⟩ := hh
    have hvw' := (Monomial.act g).injective hvw
    rwa [← hvw']

/-- Alternating orientations in the existing ordered coordinates. -/
def hexZRaw : Monomial HexIndex :=
  ⟨1, fun i => if i.2 = 0 then localKappa else localKappa⁻¹⟩

def hexLiftLocals (k : Fin 5) (i : HexIndex) : KIsometry :=
  ![![1,1,localU,localU,localU,localU],
    ![localU,1,1,localU,localV,localV],
    ![localU,localU,1,1,localU,localU],
    ![localU,localW,localW,localKappa,localKappa⁻¹,localV],
    ![localU,localU,localU,localU,1,1]] k (hexIndexEquiv i)

def hexLiftRaw (k : Fin 5) : Monomial HexIndex :=
  ⟨Equiv.swap (hexPos k.castSucc) (hexPos k.succ), hexLiftLocals k⟩

theorem hexZRaw_preserves_basis : ∀ k,
    Monomial.act hexZRaw (hexGenerators k) ∈ hexacode := by
  intro k
  rw [hexacode_systematic]
  revert k
  decide

theorem hexLiftRaw_preserves_basis : ∀ k i,
    Monomial.act (hexLiftRaw k) (hexGenerators i) ∈ hexacode := by
  intro k i
  rw [hexacode_systematic]
  revert k i
  decide

def hexZ : HexAutomorphisms := ⟨hexZRaw, monomial_mem_of_hexBasis _ hexZRaw_preserves_basis⟩
def hexLift (k : Fin 5) : HexAutomorphisms :=
  ⟨hexLiftRaw k, monomial_mem_of_hexBasis _ (hexLiftRaw_preserves_basis k)⟩

@[simp] theorem hexZ_coordinate : hexCoordinateHom hexZ = 1 := rfl
@[simp] theorem hexLift_coordinate (k : Fin 5) :
    hexCoordinateHom (hexLift k) = Equiv.swap (hexPos k.castSucc) (hexPos k.succ) := rfl

theorem hexZ_cube : hexZ ^ 3 = 1 := by
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext; intro i; rfl
  · funext i
    apply LinearEquiv.ext
    intro u
    revert i u
    decide

theorem hexZ_ne_one : hexZ ≠ 1 := by
  intro h
  have hh := congrArg (fun g : HexAutomorphisms => g.val.localMap (hexPos 0) a) h
  exact (by decide : b ≠ a) hh

theorem hexLift_sq (k : Fin 5) : hexLift k * hexLift k = 1 := by
  apply Subtype.ext
  apply Monomial.ext
  · exact Equiv.swap_mul_self _ _
  · funext i
    apply LinearEquiv.ext
    intro u
    revert k i u
    decide

theorem hexLift_inverts (k : Fin 5) : hexLift k * hexZ * (hexLift k)⁻¹ = hexZ⁻¹ := by
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext
    intro i
    revert k i
    decide
  · funext i
    apply LinearEquiv.ext
    intro u
    revert k i u
    decide

end Atlas.Codes
