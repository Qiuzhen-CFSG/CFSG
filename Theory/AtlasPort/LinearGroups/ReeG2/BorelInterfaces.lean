module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/BorelInterfaces.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.BorelSolvable
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
variable (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))

theorem root_inf_torus_eq_bot : rootSubgroup m hcard ⊓ splitTorus m = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨⟨p,hp⟩,⟨l,hl⟩⟩ := hg
  have ht : torus (F := F) m 1 = 1 := (torusHom m).map_one
  have h : rootElement m p.1 p.2.1 p.2.2 = torus m l := hp.trans hl.symm
  have hb : borelParam m (p,1) = borelParam m ((0,0,0),l) := by
    simpa only [borelParam, ht, rootElement_zero, mul_one, one_mul] using h
  have hlone : (1 : Fˣ) = l := congrArg Prod.snd (borelParam_injective m hb)
  change g = 1
  rw [← hl, ← hlone]
  exact ht

theorem borel_le_generated : borel m hcard ≤ generated F m := by
  apply sup_le (rootSubgroup_le_generated m hcard)
  rintro g ⟨l,rfl⟩
  exact Subgroup.subset_closure (Or.inl (Or.inr ⟨l,rfl⟩))

def borelTorusSection : Fˣ →* borel m hcard where
  toFun l := ⟨torus m l,
    (show splitTorus m ≤ borel m hcard from le_sup_right) ⟨l,rfl⟩⟩
  map_one' := Subtype.ext (torusHom (F := F) m).map_one
  map_mul' l k := Subtype.ext (torus_mul m l k)

theorem borel_projection_section (l : Fˣ) :
    borelTorusProjection m hcard (borelTorusSection m hcard l) = l := by
  apply Units.ext
  apply (theta F m).injective
  change theta F m (borelTorusParameter m hcard (borelTorusSection m hcard l) : F) = _
  rw [borelTorusParameter_zero_zero]
  rfl

theorem borel_projection_surjective : Function.Surjective (borelTorusProjection m hcard) :=
  fun l => ⟨borelTorusSection m hcard l,borel_projection_section m hcard l⟩

theorem borel_projection_kernel :
    (borelTorusProjection m hcard).ker = (rootToBorel m hcard).range := by
  apply le_antisymm (borelTorusProjection_ker_le_range m hcard)
  rintro g ⟨⟨_,p,rfl⟩,rfl⟩
  change borelTorusProjection m hcard _ = 1
  apply Units.ext
  apply (theta F m).injective
  change theta F m (borelTorusParameter m hcard _ : F) = theta F m 1
  rw [borelTorusParameter_zero_zero, map_one]
  change rootMatrix m p.1 p.2.1 p.2.2 0 0 = 1
  simp [rootMatrix_expanded, rootExpanded]
end Atlas.ReeG2
