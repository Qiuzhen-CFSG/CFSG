module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/DerivedSubgroup.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.RootGroup
public import Theory.AtlasPort.LinearGroups.ReeG2.Torus
public import Mathlib.GroupTheory.IsPerfect
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- The derived subgroup of the actual Ree model, viewed inside the ambient matrices. -/
def derivedAmbient (m : ℕ) : Subgroup (Ambient F) :=
  (commutator (Model F m)).map (generated F m).subtype

theorem torus_mem_generated (m : ℕ) (l : Fˣ) : torus m l ∈ generated F m :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨l,rfl⟩))

theorem root_mem_generated (m : ℕ) (hcard : Nat.card F = 3 ^ (2 * m + 1))
    (a b c : F) : rootElement m a b c ∈ generated F m :=
  rootSubgroup_le_generated m hcard ⟨(a,b,c),rfl⟩

theorem commutator_mem_derivedAmbient (m : ℕ) {g h : Ambient F}
    (hg : g ∈ generated F m) (hh : h ∈ generated F m) :
    ⁅g,h⁆ ∈ derivedAmbient m := by
  exact ⟨⁅(⟨g,hg⟩ : Model F m),⟨h,hh⟩⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _),rfl⟩

theorem conjugate_mem_derivedAmbient (m : ℕ) {g h : Ambient F}
    (hg : g ∈ generated F m) (hh : h ∈ derivedAmbient m) :
    g*h*g⁻¹ ∈ derivedAmbient m := by
  obtain ⟨x,hx,rfl⟩ := hh
  exact ⟨(⟨g,hg⟩ : Model F m)*x*(⟨g,hg⟩ : Model F m)⁻¹,
    (inferInstance : (commutator (Model F m)).Normal).conj_mem x hx ⟨g,hg⟩,rfl⟩

end Atlas.ReeG2
