module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/CompatibilityGroup.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.GeneratorCompatibility
public import Theory.AtlasPort.LinearGroups.ReeG2.TorusCompatibility
public import Theory.AtlasPort.LinearGroups.ReeG2.WeylPointAction
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Linear transformations preserving the twisted bilinear compatibility relation. -/
def compatibilityStabilizer (m : ℕ) : Subgroup (Ambient F) where
  carrier := {g | ∀ v w, pointCompatibility m v w →
    pointCompatibility m (rowEquiv g v) (rowEquiv g w)}
  one_mem' := by intro v w h; simpa using h
  mul_mem' := by
    intro g h hg hh v w hvw
    simp only [rowEquiv_mul]
    exact hh _ _ (hg _ _ hvw)
  inv_mem' := by
    intro g hg v w hvw
    let S : Set (Vector F × Vector F) := {p | pointCompatibility m p.1 p.2}
    let f : (Vector F × Vector F) → (Vector F × Vector F) :=
      fun p => (rowEquiv g p.1, rowEquiv g p.2)
    have hm : Set.MapsTo f S S := fun p hp => hg _ _ hp
    have hi : Function.Injective f := by
      intro p q hh
      exact Prod.ext ((rowEquiv g).injective (congrArg Prod.fst hh))
        ((rowEquiv g).injective (congrArg Prod.snd hh))
    have hb := (S.toFinite.injOn_iff_bijOn_of_mapsTo hm).mp hi.injOn
    obtain ⟨⟨a,b⟩,hab,he⟩ := hb.surjOn (show (v,w) ∈ S from hvw)
    have hv := congrArg Prod.fst he
    have hw := congrArg Prod.snd he
    have hc (x : Vector F) : rowEquiv g⁻¹ (rowEquiv g x) = x := by
      rw [← rowEquiv_mul,mul_inv_cancel,rowEquiv_one]
    change rowEquiv g a = v at hv
    change rowEquiv g b = w at hw
    rw [← hv,← hw,hc,hc]
    exact hab

theorem generated_preserves_pointCompatibility (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    generated F m ≤ compatibilityStabilizer m := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with (((⟨a,rfl⟩ | ⟨b,rfl⟩) | ⟨c,rfl⟩) | ⟨l,rfl⟩) | hw
  · intro v w h
    exact alpha_preserves_pointCompatibility m hcard a h
  · intro v w h
    exact beta_preserves_pointCompatibility m hcard b h
  · intro v w h
    exact gamma_preserves_pointCompatibility m hcard c h
  · intro v w h
    exact torus_preserves_pointCompatibility m hcard l h
  · have : g = upsilon := Set.mem_singleton_iff.mp hw
    subst g
    intro v w h
    rw [rowEquiv_upsilon,rowEquiv_upsilon]
    exact pointCompatibility_reverse m h

end Atlas.ReeG2
