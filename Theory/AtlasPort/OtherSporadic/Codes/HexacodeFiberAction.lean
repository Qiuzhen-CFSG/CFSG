/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeZeroFibers
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeFiberRotation

/-!
# HexacodeFiberAction

In normalized hexacode coordinates, a double-zero fiber is identified with the Kleinian
alphabet. The transported fiber rotation acts by a three-cycle on its nonzero letters,
proving transitivity on that fiber.

Source: `Atlas/Codes/HexacodeFiberAction.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def hexDoubleZeroAction (i j : HexIndex) (g : hexPointKernel i)
    (hj : g.val.val.val.perm j = j) : hexDoubleZero i j →ₗ[Bit] hexDoubleZero i j where
  toFun h := ⟨hexAction g.val.val h.val, by
    constructor
    · change g.val.val.val.localMap i (h.val.val (g.val.val.val.perm.symm i)) = 0
      rw [hexPointStabilizer_inv_fixed]
      rw [show h.val.val i = 0 from h.prop.1,map_zero]
    · change g.val.val.val.localMap j (h.val.val (g.val.val.val.perm.symm j)) = 0
      rw [(Equiv.symm_apply_eq _).mpr hj.symm]
      rw [show h.val.val j = 0 from h.prop.2,map_zero]⟩
  map_add' u v := Subtype.ext (map_add _ _ _)
  map_smul' t u := Subtype.ext (map_smul _ _ _)

def normalizedInput (m : Monomial HexIndex) (i : Fin 3) : HexIndex := m.perm.symm (firstThree i)

theorem normalizedInput_injective (m : Monomial HexIndex) : Function.Injective (normalizedInput m) :=
  m.perm.symm.injective.comp firstThree.injective

def normalizedFiberEquiv (m : Monomial HexIndex) :
    hexDoubleZero (normalizedInput m 0) (normalizedInput m 1) ≃ₗ[Bit] K :=
  (hexDoubleZeroEquiv _ _ (normalizedInput m 2)
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (normalizedInput_injective m h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (normalizedInput_injective m h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (normalizedInput_injective m h))).trans
    (m.localMap (firstThree 2))

theorem normalizedFiberEquiv_rotation (m : Monomial HexIndex)
    (hm : ∀ w : HexWord, w ∈ hexacode ↔ Monomial.act m w ∈ KleinNormalWords)
    (u : hexDoubleZero (normalizedInput m 0) (normalizedInput m 1)) :
    normalizedFiberEquiv m
      (hexDoubleZeroAction _ _ (transportedFiberKernel m hm) (transportedFiberRotation_fixed m 1) u) =
      localKappa⁻¹ (normalizedFiberEquiv m u) :=
  transportedFiberRotation_coordinate m u.val.val


theorem localKappa_inverse_twice (u : K) : localKappa⁻¹ (localKappa⁻¹ u) = localKappa u := by
  apply Prod.ext <;> simp [localKappa_inv_apply]
  ring_nf
  simp only [bit_two,mul_zero,zero_add]

theorem normalized_fiber_transitive (m : Monomial HexIndex)
    (hm : ∀ w : HexWord, w ∈ hexacode ↔ Monomial.act m w ∈ KleinNormalWords)
    (u v : hexDoubleZero (normalizedInput m 0) (normalizedInput m 1))
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : hexPointKernel (normalizedInput m 0),
      g.val.val.val.perm (normalizedInput m 1) = normalizedInput m 1 ∧
      hexAction g.val.val u.val = v.val := by
  let e := normalizedFiberEquiv m
  let r := transportedFiberKernel m hm
  let f := hexDoubleZeroAction _ _ r (transportedFiberRotation_fixed m 1)
  have hf (w) : e (f w) = localKappa⁻¹ (e w) := normalizedFiberEquiv_rotation m hm w
  have hu' : e u ≠ 0 := fun h => hu (e.map_eq_zero_iff.mp h)
  have hv' : e v ≠ 0 := fun h => hv (e.map_eq_zero_iff.mp h)
  rcases klein_inverse_cycle_transitive (e u) (e v) hu' hv' with h | h | h
  · have he : v = u := e.injective h
    subst v
    exact ⟨1,rfl,rfl⟩
  · have he : v = f u := e.injective (h.trans (hf u).symm)
    subst v
    exact ⟨r,transportedFiberRotation_fixed m 1,rfl⟩
  · have he : v = f (f u) := by
      apply e.injective
      calc
        e v = localKappa (e u) := h
        _ = localKappa⁻¹ (localKappa⁻¹ (e u)) := (localKappa_inverse_twice _).symm
        _ = localKappa⁻¹ (e (f u)) := congrArg (fun z => localKappa⁻¹ z) (hf u).symm
        _ = e (f (f u)) := (hf (f u)).symm
    subst v
    refine ⟨r*r,?_,?_⟩
    · change r.val.val.val.perm (r.val.val.val.perm (normalizedInput m 1)) = normalizedInput m 1
      have hr : r.val.val.val.perm (normalizedInput m 1) = normalizedInput m 1 :=
        transportedFiberRotation_fixed m 1
      rw [hr,hr]
    · change hexAction (r.val.val*r.val.val) u.val = hexAction r.val.val (hexAction r.val.val u.val)
      rw [map_mul]
      rfl

end Atlas.Codes
