/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeKernel
public import Mathlib.GroupTheory.OrderOfElement

/-!
# HexacodeOrder

The full monomial hexacode automorphism group has order 2160. Adjacent-transposition
lifts give surjectivity onto the symmetric coordinate group, the kernel is cyclic of
order three, and these lifts together with the scalar generate the group.

Source: `Atlas/Codes/HexacodeOrder.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

/-- The coordinate quotient, transported to the specified six-position order. -/
def hexCoordinateSixHom : HexAutomorphisms →* Equiv.Perm (Fin 6) :=
  hexIndexEquiv.permCongrHom.toMonoidHom.comp hexCoordinateHom

theorem hexSix_eq_one (g : HexAutomorphisms) :
    hexCoordinateSixHom g = 1 ↔ hexCoordinateHom g = 1 := by
  exact hexIndexEquiv.permCongrHom.map_eq_one_iff

@[simp] theorem hexLift_six (k : Fin 5) :
    hexCoordinateSixHom (hexLift k) = Equiv.swap k.castSucc k.succ := by
  apply Equiv.ext
  intro i
  revert k i
  decide

@[simp] theorem hexZ_six : hexCoordinateSixHom hexZ = 1 := (hexSix_eq_one _).mpr hexZ_coordinate

theorem adjacent_closure : Subgroup.closure
    (Set.range (fun k : Fin 5 => Equiv.swap k.castSucc k.succ)) = ⊤ :=
  Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)

theorem hexCoordinateSix_surjective : Function.Surjective hexCoordinateSixHom := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← adjacent_closure, Subgroup.closure_le]
  rintro _ ⟨k,rfl⟩
  exact ⟨hexLift k,hexLift_six k⟩

theorem hexCoordinateHom_surjective : Function.Surjective hexCoordinateHom := by
  intro σ
  obtain ⟨g,hg⟩ := hexCoordinateSix_surjective (hexIndexEquiv.permCongrHom σ)
  exact ⟨g,hexIndexEquiv.permCongrHom.injective hg⟩

theorem hexZ_order : orderOf hexZ = 3 := orderOf_eq_prime hexZ_cube hexZ_ne_one

theorem hexCoordinate_kernel : hexCoordinateHom.ker = Subgroup.zpowers hexZ := by
  apply le_antisymm
  · intro g hg
    rcases hex_kernel_trichotomy g hg with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    exact hexZ_coordinate

theorem hexCoordinateSix_kernel : hexCoordinateSixHom.ker = Subgroup.zpowers hexZ := by
  rw [← hexCoordinate_kernel]
  ext g
  exact hexSix_eq_one g

theorem hex_kernel_card : Nat.card hexCoordinateHom.ker = 3 := by
  rw [hexCoordinate_kernel, Nat.card_zpowers, hexZ_order]

theorem hexAutomorphisms_card : Nat.card HexAutomorphisms = 2160 := by
  have h := hexCoordinateSixHom.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hexCoordinateSix_surjective,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (Equiv.Perm (Fin 6))) ≃* _).toEquiv,
    hexCoordinateSix_kernel, Nat.card_zpowers, hexZ_order,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
  norm_num at h
  exact h.symm

def hexGeneratingSet : Set HexAutomorphisms := insert hexZ (Set.range hexLift)

theorem hexAutomorphisms_generated : Subgroup.closure hexGeneratingSet = ⊤ := by
  let D := Subgroup.closure hexGeneratingSet
  have hz : hexZ ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have hs (k : Fin 5) : hexLift k ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨k,rfl⟩)
  let f : D →* Equiv.Perm (Fin 6) := hexCoordinateSixHom.comp D.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← adjacent_closure, Subgroup.closure_le]
    rintro _ ⟨k,rfl⟩
    exact ⟨⟨hexLift k,hs k⟩,hexLift_six k⟩
  apply top_unique
  intro g _
  obtain ⟨d,hd⟩ := hf (hexCoordinateSixHom g)
  have hk : g * d.val⁻¹ ∈ hexCoordinateSixHom.ker := by
    change hexCoordinateSixHom (g * d.val⁻¹) = 1
    change hexCoordinateSixHom d.val = hexCoordinateSixHom g at hd
    rw [map_mul, map_inv, hd, mul_inv_cancel]
  have hkd : g * d.val⁻¹ ∈ D := by
    rw [hexCoordinateSix_kernel] at hk
    exact (Subgroup.zpowers_le.mpr hz) hk
  have hh := D.mul_mem hkd d.prop
  simpa using hh

end Atlas.Codes
