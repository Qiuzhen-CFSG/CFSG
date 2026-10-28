module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/ProjectiveAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.RootPointAction
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxHeartbeats 2000000

@[simp] theorem rowEquiv_apply (g : Ambient F) (v : Vector F) :
    rowEquiv g v = v ᵥ* g.val := rfl

theorem pointRight_one : pointRight (1 : Ambient F) = id := by
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    change Projectivization.mk F (v ᵥ* (1 : Mat F)) _ = Projectivization.mk F v hv
    simp only [Matrix.vecMul_one]

theorem pointRight_mul (g h : Ambient F) :
    pointRight (g*h) = pointRight h ∘ pointRight g := by
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    change Projectivization.mk F (v ᵥ* (g*h).val) _ =
      Projectivization.mk F ((v ᵥ* g.val) ᵥ* h.val) _
    simp only [Matrix.vecMul_vecMul, Units.val_mul]

theorem pointRight_injective (g : Ambient F) : Function.Injective (pointRight g) :=
  Projectivization.map_injective (rowEquiv g).toLinearMap (rowEquiv g).injective

theorem pointRight_zero_root (m : ℕ) (hcard : Nat.card F = 3^(2*m+1)) (a b c : F) :
    pointRight (rootElement m a b c) (affinePoint m 0 0 0) = affinePoint m a b c := by
  rw [pointRight_affine_root m hcard]
  simp

theorem root_regular_on_affine (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (a b c x y z : F) :
    ∃! g : rootSubgroup m hcard,
      pointRight g.val (affinePoint m a b c) = affinePoint m x y z := by
  let u : rootSubgroup m hcard := ⟨rootElement m a b c,⟨(a,b,c),rfl⟩⟩
  let v : rootSubgroup m hcard := ⟨rootElement m x y z,⟨(x,y,z),rfl⟩⟩
  have hu : pointRight u.val (affinePoint m 0 0 0) = affinePoint m a b c :=
    pointRight_zero_root m hcard a b c
  have hv : pointRight v.val (affinePoint m 0 0 0) = affinePoint m x y z :=
    pointRight_zero_root m hcard x y z
  have hinj : Function.Injective (fun g : rootSubgroup m hcard =>
      pointRight g.val (affinePoint m 0 0 0)) := by
    intro g h he
    dsimp only at he
    obtain ⟨⟨r,s,t⟩,hr⟩ := g.property
    obtain ⟨⟨r',s',t'⟩,hr'⟩ := h.property
    rw [← hr, ← hr', pointRight_zero_root m hcard, pointRight_zero_root m hcard] at he
    have hp : (r,s,t) = (r',s',t') :=
      affinePoint_injective m (a₁ := (r,s,t)) (a₂ := (r',s',t')) he
    obtain ⟨hr1,hr2⟩ := Prod.mk.inj hp
    obtain ⟨hs,ht⟩ := Prod.mk.inj hr2
    subst r'; subst s'; subst t'
    exact Subtype.ext (hr.symm.trans hr')
  refine ⟨u⁻¹*v,?_,?_⟩
  · rw [← hu]
    change (pointRight ((u⁻¹*v).val) ∘ pointRight u.val) (affinePoint m 0 0 0) = _
    rw [← pointRight_mul]
    change pointRight (u * (u⁻¹*v)).val (affinePoint m 0 0 0) = _
    simpa using hv
  · intro g hg
    have hprod : u*g = v := hinj (by
      change pointRight (u.val*g.val) _ = _
      rw [pointRight_mul]
      change pointRight g.val (pointRight u.val _) = _
      rw [hu,hg]
      exact hv.symm)
    exact (eq_inv_mul_iff_mul_eq).mpr hprod
end Atlas.ReeG2
