/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeFiberAction

/-!
# HexacodeFiberTransport

Monomial automorphisms transport double-zero fibers and conjugate local coordinate
kernels. Two-coordinate transitivity moves an arbitrary fiber to a normalized one, where
the explicit rotation proves transitivity on nonzero words.

Source: `Atlas/Codes/HexacodeFiberTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def hexDoubleZeroTransport (g : HexAutomorphisms) (i j : HexIndex) :
    hexDoubleZero i j ≃ₗ[Bit] hexDoubleZero (g.val.perm i) (g.val.perm j) where
  toFun u := ⟨hexAction g u.val, by
    constructor
    · change g.val.localMap (g.val.perm i) (u.val.val (g.val.perm.symm (g.val.perm i))) = 0
      rw [Equiv.symm_apply_apply,show u.val.val i = 0 from u.prop.1,map_zero]
    · change g.val.localMap (g.val.perm j) (u.val.val (g.val.perm.symm (g.val.perm j))) = 0
      rw [Equiv.symm_apply_apply,show u.val.val j = 0 from u.prop.2,map_zero]⟩
  invFun v := ⟨hexAction g⁻¹ v.val, by
    constructor
    · change (g.val.localMap (g.val.perm i))⁻¹ (v.val.val (g.val.perm i)) = 0
      rw [show v.val.val (g.val.perm i) = 0 from v.prop.1,map_zero]
    · change (g.val.localMap (g.val.perm j))⁻¹ (v.val.val (g.val.perm j)) = 0
      rw [show v.val.val (g.val.perm j) = 0 from v.prop.2,map_zero]⟩
  left_inv u := by
    apply Subtype.ext
    change hexAction g⁻¹ (hexAction g u.val) = u.val
    rw [← LinearEquiv.mul_apply,← map_mul,inv_mul_cancel,map_one]
    rfl
  right_inv v := by
    apply Subtype.ext
    change hexAction g (hexAction g⁻¹ v.val) = v.val
    rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl
  map_add' u v := Subtype.ext (map_add _ _ _)
  map_smul' t u := Subtype.ext (map_smul _ _ _)

theorem hexPointKernel_conjugate_fixed (g : HexAutomorphisms) (i : HexIndex) (h : hexPointKernel i) :
    (g*h.val.val*g⁻¹).val.perm (g.val.perm i) = g.val.perm i := by
  change g.val.perm (h.val.val.val.perm (g.val.perm.symm (g.val.perm i))) = g.val.perm i
  rw [Equiv.symm_apply_apply,h.val.prop]

theorem hexPointKernel_conjugate_local (g : HexAutomorphisms) (i : HexIndex) (h : hexPointKernel i) :
    (g*h.val.val*g⁻¹).val.localMap (g.val.perm i) = 1 := by
  change (g.val*h.val.val.val*g.val⁻¹).localMap (g.val.perm i) = 1
  simp only [Monomial.mul_local,Monomial.inv_local,Monomial.mul_perm,Equiv.Perm.mul_def]
  simp only [Equiv.symm_apply_apply]
  have hh : h.val.val.val.localMap i = 1 := h.prop
  rw [hh,mul_one]
  simp only [Equiv.symm_trans_apply,Equiv.symm_apply_apply,hexPointStabilizer_inv_fixed]
  exact mul_inv_cancel _

def hexPointKernelConjugate (g : HexAutomorphisms) (i : HexIndex) (h : hexPointKernel i) :
    hexPointKernel (g.val.perm i) :=
  ⟨⟨g*h.val.val*g⁻¹,hexPointKernel_conjugate_fixed g i h⟩,hexPointKernel_conjugate_local g i h⟩

theorem hex_two_coordinate_transitive (i j k l : HexIndex) (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ g : HexAutomorphisms, g.val.perm i = k ∧ g.val.perm j = l := by
  obtain ⟨σ,hi,hj⟩ := (MulAction.is_two_pretransitive_iff.mp
    (Equiv.Perm.isMultiplyPretransitive HexIndex 2)) hij hkl
  obtain ⟨g,hg⟩ := hexCoordinateHom_surjective σ
  exact ⟨g,by change hexCoordinateHom g i = k; rw [hg]; exact hi,
    by change hexCoordinateHom g j = l; rw [hg]; exact hj⟩


theorem hex_fiber_transitive (i j : HexIndex) (hij : i ≠ j)
    (u v : hexDoubleZero i j) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ h : hexPointKernel i, h.val.val.val.perm j = j ∧ hexAction h.val.val u.val = v.val := by
  obtain ⟨m,hm⟩ := hex_mds_normal_form hexacode hexacode_isHexMDS
  let i0 := normalizedInput m 0
  let j0 := normalizedInput m 1
  have hi0 : i0 ≠ j0 := fun h => (by decide : (0 : Fin 3) ≠ 1) (normalizedInput_injective m h)
  obtain ⟨g,hi,hj⟩ := hex_two_coordinate_transitive i0 j0 i j hi0 hij
  rcases hi with rfl
  rcases hj with rfl
  let e := hexDoubleZeroTransport g i0 j0
  have hu' : e.symm u ≠ 0 := fun h => hu (e.symm.map_eq_zero_iff.mp h)
  have hv' : e.symm v ≠ 0 := fun h => hv (e.symm.map_eq_zero_iff.mp h)
  obtain ⟨r,hr,he⟩ := normalized_fiber_transitive m hm (e.symm u) (e.symm v) hu' hv'
  refine ⟨hexPointKernelConjugate g i0 r,?_,?_⟩
  · change g.val.perm (r.val.val.val.perm (g.val.perm.symm (g.val.perm j0))) = g.val.perm j0
    rw [Equiv.symm_apply_apply,hr]
  · have hU : hexAction g (e.symm u).val = u.val := congrArg Subtype.val (e.apply_symm_apply u)
    have hV : hexAction g (e.symm v).val = v.val := congrArg Subtype.val (e.apply_symm_apply v)
    change hexAction (g*r.val.val*g⁻¹) u.val = v.val
    rw [← hU,map_mul,map_mul,map_inv]
    change hexAction g (hexAction r.val.val
      ((hexAction g).symm (hexAction g (e.symm u).val))) = v.val
    rw [LinearEquiv.symm_apply_apply,he]
    exact hV

end Atlas.Codes
