module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/BorelPointAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.TorusPointAction
public import Theory.AtlasPort.LinearGroups.ReeG2.BorelInterfaces
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem borel_preserves_pointSet (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (g : borel m hcard) {p : Projective F} (hp : p ∈ pointSet m) :
    pointRight g.val p ∈ pointSet m := by
  obtain ⟨⟨⟨a,b,c⟩,l⟩,rfl⟩ := (borelEquiv m hcard).surjective g
  change pointRight (rootElement m a b c * torus m l) p ∈ pointSet m
  rw [pointRight_mul]
  exact torus_preserves_pointSet m hcard l
    (root_preserves_pointSet m hcard ⟨rootElement m a b c,⟨(a,b,c),rfl⟩⟩ hp)

theorem borel_fixes_infinity (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (g : borel m hcard) : pointRight g.val infinityPoint = infinityPoint := by
  obtain ⟨⟨⟨a,b,c⟩,l⟩,rfl⟩ := (borelEquiv m hcard).surjective g
  change pointRight (rootElement m a b c * torus m l) infinityPoint = _
  rw [pointRight_mul]
  change pointRight (torus m l) (pointRight (rootElement m a b c) infinityPoint) = _
  rw [pointRight_infinity_root,pointRight_infinity_torus]

theorem borel_fixes_zero_iff_torus (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (g : borel m hcard) :
    pointRight g.val (affinePoint m 0 0 0) = affinePoint m 0 0 0 ↔
      g.val ∈ splitTorus m := by
  constructor
  · intro hg
    obtain ⟨⟨⟨a,b,c⟩,l⟩,rfl⟩ := (borelEquiv m hcard).surjective g
    change pointRight (rootElement m a b c * torus m l) (affinePoint m 0 0 0) = _ at hg
    rw [pointRight_mul] at hg
    have hz : pointRight (rootElement m a b c) (affinePoint m 0 0 0) = affinePoint m 0 0 0 :=
      pointRight_injective (torus m l) (hg.trans (pointRight_zero_torus m l).symm)
    rw [pointRight_zero_root m hcard] at hz
    have he : (a,b,c) = ((0 : F),0,0) := affinePoint_injective m hz
    have ha := congrArg Prod.fst he
    have hb := congrArg (fun p : F × F × F => p.2.1) he
    have hc := congrArg (fun p : F × F × F => p.2.2) he
    dsimp only at ha hb hc
    subst a; subst b; subst c
    refine ⟨l,?_⟩
    change torus m l = rootElement m 0 0 0 * torus m l
    rw [rootElement_zero,one_mul]
  · rintro ⟨l,hl⟩
    rw [← hl]
    exact pointRight_zero_torus m l

theorem borel_action_faithful (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (g : borel m hcard)
    (hg : ∀ p ∈ pointSet m, pointRight g.val p = p) : g = 1 := by
  have hz := hg (affinePoint m 0 0 0) ⟨some (0,0,0),rfl⟩
  obtain ⟨l,hl⟩ := (borel_fixes_zero_iff_torus m hcard g).mp hz
  change torus m l = g.val at hl
  have hc := hg (affinePoint m 0 0 1) ⟨some (0,0,1),rfl⟩
  rw [← hl,pointRight_affine_torus m hcard] at hc
  simp only [zero_mul,zero_div] at hc
  have hp : ((0 : F),(0 : F),1/(l : F)) = (0,0,1) :=
    affinePoint_injective m (a₁ := (0,0,1/(l : F))) (a₂ := (0,0,1)) hc
  have he : 1/(l : F) = 1 := congrArg (fun p : F × F × F => p.2.2) hp
  have hlone : l = 1 := Units.ext ((div_eq_one_iff_eq (Units.ne_zero l)).mp he).symm
  apply Subtype.ext
  rw [← hl,hlone]
  exact (torusHom m).map_one
end Atlas.ReeG2
