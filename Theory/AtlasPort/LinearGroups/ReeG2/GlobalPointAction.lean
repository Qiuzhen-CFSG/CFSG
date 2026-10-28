module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/GlobalPointAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.WeylPointAction
public import Theory.AtlasPort.LinearGroups.ReeG2.TorusPointAction
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Matrix subgroup preserving the concrete finite Ree point set. -/
def pointSetStabilizer (m : ℕ) : Subgroup (Ambient F) where
  carrier := {g | Set.MapsTo (pointRight g) (pointSet m) (pointSet m)}
  one_mem' := by simp [pointRight_one, Set.mapsTo_id]
  mul_mem' := by
    intro g h hg hh p hp
    rw [pointRight_mul]
    exact hh (hg hp)
  inv_mem' := by
    intro g hg p hp
    letI : Finite (pointSet (F := F) m) := Finite.of_equiv (Option (F × F × F)) (pointEquiv m)
    have hb := ((pointSet (F := F) m).toFinite.injOn_iff_bijOn_of_mapsTo hg).mp
      (pointRight_injective g).injOn
    obtain ⟨x,hx,hxp⟩ := hb.surjOn hp
    have he : pointRight g⁻¹ (pointRight g x) = x := by
      have hh := congrFun (pointRight_mul g g⁻¹) x
      simpa [pointRight_one] using hh.symm
    rw [← hxp, he]
    exact hx

theorem generated_preserves_pointSet (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    generated F m ≤ pointSetStabilizer m := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with (((⟨a,rfl⟩ | ⟨b,rfl⟩) | ⟨c,rfl⟩) | ⟨l,rfl⟩) | hw
  · have he : alpha m a = rootElement m a 0 0 := by simp [rootElement]
    rw [he]
    intro p hp
    exact root_preserves_pointSet m hcard ⟨_,⟨(a,0,0),rfl⟩⟩ hp
  · have he : beta m b = rootElement m 0 b 0 := by simp [rootElement]
    rw [he]
    intro p hp
    exact root_preserves_pointSet m hcard ⟨_,⟨(0,b,0),rfl⟩⟩ hp
  · have he : gamma m c = rootElement m 0 0 c := by simp [rootElement]
    rw [he]
    intro p hp
    exact root_preserves_pointSet m hcard ⟨_,⟨(0,0,c),rfl⟩⟩ hp
  · intro p hp
    exact torus_preserves_pointSet m hcard l hp
  · have : g = upsilon := Set.mem_singleton_iff.mp hw
    subst g
    exact upsilon_preserves_pointSet m hcard

/-- Left action convention: a matrix acts by right multiplication by its inverse. -/
def pointAction (m : ℕ) (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    MulAction (Model F m) (pointSet (F := F) m) where
  smul g p := ⟨pointRight g.val⁻¹ p.val,
    generated_preserves_pointSet m hcard ((generated F m).inv_mem g.property) p.property⟩
  one_smul p := by apply Subtype.ext; exact congrFun pointRight_one p.val
  mul_smul g h p := by
    apply Subtype.ext
    change pointRight ((g.val*h.val)⁻¹) p.val =
      pointRight g.val⁻¹ (pointRight h.val⁻¹ p.val)
    rw [mul_inv_rev,pointRight_mul]
    rfl

end Atlas.ReeG2
