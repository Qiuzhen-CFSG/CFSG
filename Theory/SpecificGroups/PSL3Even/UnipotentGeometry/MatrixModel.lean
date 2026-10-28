module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The marked unitriangular group inside PSL₃(F)

An upper-unitriangular scalar matrix is the identity. Consequently the concrete
coordinate group embeds faithfully in PSL₃(F), and its root planes and center
retain their literal matrix representatives. This supplies model equivalences,
not an assertion that the image is Sylow or that an arbitrary amalgam is this model.

The scalar-kernel proof adapts Gerald Höhn's
`Atlas/LinearGroups/UnitriangularThreeProjective.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, to CFSG coordinates and Lean 4.33.
The ATLAS Research and Attribution License 1.0 applies to the adapted proof;
see `LICENSES/ATLAS.txt` and `docs/atlas-porting.md`.
Source: Aschbacher--Smith §5.3.5--5.3.7, printed p. 660 (PDF p. 677).
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F]

def projective : U F →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
  (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F))).comp
    (specialLinear F)

theorem projective_injective : Function.Injective (projective F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  have hc : specialLinear F a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨r, _, he⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have hd := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) he
  have hr : r = 1 := hd
  apply specialLinear_injective F
  rw [map_one]
  apply Subtype.ext
  simpa [hr] using he.symm

def projectiveEquiv : U F ≃* (projective F).range :=
  MonoidHom.ofInjective (projective_injective F)

def projectivePlane₁ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
  (V₁ F).map (projective F)
def projectivePlane₂ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
  (V₂ F).map (projective F)
def projectiveCenter : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
  (Z F).map (projective F)

theorem mem_projectivePlane₁ (g : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    g ∈ projectivePlane₁ F ↔ ∃ a c : F, projective F ⟨a,0,c⟩ = g := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.x,u.c,congrArg (projective F) (U.ext rfl ((mem_V₁ F u).mp hu).symm rfl)⟩
  · rintro ⟨a,c,rfl⟩
    exact ⟨⟨a,0,c⟩,(mem_V₁ F _).mpr rfl,rfl⟩

theorem mem_projectivePlane₂ (g : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    g ∈ projectivePlane₂ F ↔ ∃ b c : F, projective F ⟨0,b,c⟩ = g := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.y,u.c,congrArg (projective F) (U.ext ((mem_V₂ F u).mp hu).symm rfl rfl)⟩
  · rintro ⟨b,c,rfl⟩
    exact ⟨⟨0,b,c⟩,(mem_V₂ F _).mpr rfl,rfl⟩

theorem mem_projectiveCenter (g : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    g ∈ projectiveCenter F ↔ ∃ c : F, projective F ⟨0,0,c⟩ = g := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨hx,hy⟩ := (mem_Z F u).mp hu
    exact ⟨u.c,congrArg (projective F) (U.ext hx.symm hy.symm rfl)⟩
  · rintro ⟨c,rfl⟩
    exact ⟨⟨0,0,c⟩,(mem_Z F _).mpr ⟨rfl,rfl⟩,rfl⟩

theorem projective_range_card [Finite F] : Nat.card (projective F).range = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (projectiveEquiv F).toEquiv, card_U]

/-- The centralizer computation holds inside the actual projective matrix image. -/
theorem projective_involution_geometry [CharP F 2]
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (hg : g ∈ (projective F).range) (hpow : g ^ 2 = 1) (hz : g ∉ projectiveCenter F) :
    (projective F).range ⊓ Subgroup.centralizer ({g} : Set _) = projectivePlane₁ F ∨
    (projective F).range ⊓ Subgroup.centralizer ({g} : Set _) = projectivePlane₂ F :=
  marked_involution_geometry F _ (projectiveEquiv F) g hg hpow hz

end Matrix.PSL3Even.UnipotentGeometry
