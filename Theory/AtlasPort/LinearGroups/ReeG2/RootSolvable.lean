module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/RootSolvable.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.RootGroup
public import Mathlib.GroupTheory.Solvable
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
variable (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))

def rootFirst : rootSubgroup m hcard →* Multiplicative F where
  toFun g := Multiplicative.ofAdd ((rootParameterEquiv m hcard).symm g).1
  map_one' := by
    have h : (1 : rootSubgroup m hcard) = rootParameterEquiv m hcard (0,0,0) :=
      Subtype.ext (rootElement_zero m).symm
    rw [h, Equiv.symm_apply_apply]
    rfl
  map_mul' := by
    intro g h
    obtain ⟨⟨a,b,c⟩,rfl⟩ := (rootParameterEquiv m hcard).surjective g
    obtain ⟨⟨d,e,f⟩,rfl⟩ := (rootParameterEquiv m hcard).surjective h
    have hp : rootParameterEquiv m hcard (a,b,c) * rootParameterEquiv m hcard (d,e,f) =
        rootParameterEquiv m hcard
          (a+d,b+e-a*(theta F m d)^3,
            c+f-d*b+a*(theta F m d)^3*d-a^2*(theta F m d)^3) := by
      apply Subtype.ext
      exact rootElement_mul m hcard a b c d e f
    rw [hp]
    simp only [Equiv.symm_apply_apply]
    rfl

def rootLower : Multiplicative (F × F) →* rootSubgroup m hcard where
  toFun p := rootParameterEquiv m hcard (0,p.toAdd.1,p.toAdd.2)
  map_one' := Subtype.ext (rootElement_zero m)
  map_mul' := by
    intro p q
    apply Subtype.ext
    change rootElement m 0 (p.toAdd.1+q.toAdd.1) (p.toAdd.2+q.toAdd.2) =
      rootElement m 0 p.toAdd.1 p.toAdd.2 * rootElement m 0 q.toAdd.1 q.toAdd.2
    rw [rootElement_mul m hcard]
    simp

theorem rootFirst_ker_le_range :
    (rootFirst m hcard).ker ≤ (rootLower m hcard).range := by
  intro g hg
  obtain ⟨⟨a,b,c⟩,rfl⟩ := (rootParameterEquiv m hcard).surjective g
  change Multiplicative.ofAdd ((rootParameterEquiv m hcard).symm
    (rootParameterEquiv m hcard (a,b,c))).1 = 1 at hg
  rw [Equiv.symm_apply_apply] at hg
  have ha : a = 0 := congrArg Multiplicative.toAdd hg
  subst a
  exact ⟨Multiplicative.ofAdd (b,c),rfl⟩

theorem rootSubgroup_solvable : Group.IsSolvable (rootSubgroup m hcard) :=
  Group.isSolvable_of_ker_le_range (rootLower m hcard) (rootFirst m hcard)
    (rootFirst_ker_le_range m hcard)
end Atlas.ReeG2
