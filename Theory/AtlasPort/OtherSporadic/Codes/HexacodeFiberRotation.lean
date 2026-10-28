/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeUniqueness
public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodePointAlternating
public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodeZeroCoordinate

/-!
# HexacodeFiberRotation

An explicit monomial rotation preserves the normalized hexacode graph and fixes its
input positions. Conjugating by a normalizing monomial produces a local-kernel element
whose action cycles the nonzero letters in a fiber.

Source: `Atlas/Codes/HexacodeFiberRotation.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

/-- The output three-cycle with identity local map on the first input. -/
def normalFiberRotation : Monomial HexIndex where
  perm := Equiv.swap (lastThree 0) (lastThree 1) * Equiv.swap (lastThree 0) (lastThree 2)
  localMap p := Fin.addCases ![1,localKappa,localKappa⁻¹] (fun _ : Fin 3 => 1) (hexIndexEquiv p)

theorem normalFiberRotation_first (i : Fin 3) :
    normalFiberRotation.perm.symm (firstThree i) = firstThree i := by
  revert i
  decide

theorem normalFiberRotation_last (i : Fin 3) :
    normalFiberRotation.perm.symm (lastThree i) = lastThree (![1,2,0] i) := by
  revert i
  decide

theorem normalFiberRotation_local_first (i : Fin 3) :
    normalFiberRotation.localMap (firstThree i) = ![1,localKappa,localKappa⁻¹] i := by
  simp [normalFiberRotation,firstThree,hexPos]

theorem normalFiberRotation_local_last (i : Fin 3) :
    normalFiberRotation.localMap (lastThree i) = 1 := by
  fin_cases i <;> rfl

/-- Symbolic graph identity; the only coordinate cases are the six graph positions. -/
theorem normalFiberRotation_graph (x : Fin 3 → K) :
    Monomial.act normalFiberRotation (kleinGraphWord (kleinNormalMatrix localKappa) x) =
      kleinGraphWord (kleinNormalMatrix localKappa)
        (fun i => (![1,localKappa,localKappa⁻¹] i) (x i)) := by
  funext p
  rcases hexIndex_first_or_last p with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · simp only [Monomial.act_apply,normalFiberRotation_first,normalFiberRotation_local_first,
      kleinGraphWord_first]
  · simp only [Monomial.act_apply,normalFiberRotation_last,normalFiberRotation_local_last,
      LinearEquiv.coe_one, id_eq, kleinGraphWord_last]
    fin_cases i <;> apply Prod.ext <;>
      simp [kleinNormalMatrix,Fin.sum_univ_succ,localKappa_inv_apply] <;> ring_nf <;> simp only [bit_two, mul_zero, zero_add]


theorem normalFiberRotation_preserving (w : HexWord) :
    w ∈ KleinNormalWords ↔ Monomial.act normalFiberRotation w ∈ KleinNormalWords := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨_, (normalFiberRotation_graph x).symm⟩
  · rintro ⟨x,hx⟩
    let y : Fin 3 → K := fun i => (![1,localKappa,localKappa⁻¹] i)⁻¹ (x i)
    have hy : (fun i => (![1,localKappa,localKappa⁻¹] i) (y i)) = x := by
      funext i
      exact LinearEquiv.apply_symm_apply _ _
    refine ⟨y, (Monomial.act normalFiberRotation).injective ?_⟩
    rw [normalFiberRotation_graph, hy]
    exact hx

theorem normalFiberRotation_fixed_inputs (i : Fin 3) :
    normalFiberRotation.perm (firstThree i) = firstThree i :=
  (Equiv.eq_symm_apply _).mp (normalFiberRotation_first i).symm

theorem normalFiberRotation_first_local_identity :
    normalFiberRotation.localMap (firstThree 0) = 1 := normalFiberRotation_local_first 0

/-- The four-element alphabet calculation, independent of the global group. -/
theorem klein_inverse_cycle_transitive (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) :
    v = u ∨ v = localKappa⁻¹ u ∨ v = localKappa u := by
  revert u v
  decide

def transportedFiberRotation (m : Monomial HexIndex) : Monomial HexIndex :=
  m⁻¹ * normalFiberRotation * m

theorem transportedFiberRotation_preserving (m : Monomial HexIndex)
    (hm : ∀ w : HexWord, w ∈ hexacode ↔ Monomial.act m w ∈ KleinNormalWords) (w : HexWord) :
    w ∈ hexacode ↔ Monomial.act (transportedFiberRotation m) w ∈ hexacode := by
  rw [hm,hm,← Monomial.act_mul]
  have he : m * transportedFiberRotation m = normalFiberRotation * m := by
    simp [transportedFiberRotation,mul_assoc]
  rw [he,Monomial.act_mul]
  exact normalFiberRotation_preserving _


theorem transportedFiberRotation_fixed (m : Monomial HexIndex) (i : Fin 3) :
    (transportedFiberRotation m).perm (m.perm.symm (firstThree i)) = m.perm.symm (firstThree i) := by
  simp [transportedFiberRotation,Equiv.Perm.mul_apply,normalFiberRotation_fixed_inputs]

theorem transportedFiberRotation_local (m : Monomial HexIndex) :
    (transportedFiberRotation m).localMap (m.perm.symm (firstThree 0)) = 1 := by
  simp [transportedFiberRotation,Monomial.mul_local,Monomial.inv_local,
    Equiv.Perm.mul_def,Equiv.Perm.inv_def,normalFiberRotation_first,normalFiberRotation_first_local_identity]

def transportedFiberKernel (m : Monomial HexIndex)
    (hm : ∀ w : HexWord, w ∈ hexacode ↔ Monomial.act m w ∈ KleinNormalWords) :
    hexPointKernel (m.perm.symm (firstThree 0)) :=
  ⟨⟨⟨transportedFiberRotation m,transportedFiberRotation_preserving m hm⟩,
    transportedFiberRotation_fixed m 0⟩,transportedFiberRotation_local m⟩

theorem transportedFiberRotation_coordinate (m : Monomial HexIndex) (w : HexWord) :
    Monomial.act m (Monomial.act (transportedFiberRotation m) w) (firstThree 2) =
      localKappa⁻¹ (Monomial.act m w (firstThree 2)) := by
  rw [← Monomial.act_mul]
  have he : m * transportedFiberRotation m = normalFiberRotation * m := by
    simp [transportedFiberRotation,mul_assoc]
  rw [he,Monomial.act_mul,Monomial.act_apply,normalFiberRotation_first,
    normalFiberRotation_local_first]
  rfl

end Atlas.Codes
