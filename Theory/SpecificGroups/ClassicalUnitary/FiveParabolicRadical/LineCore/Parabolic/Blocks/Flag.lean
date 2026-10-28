module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Blocks.Product

/-!
# The flag criterion for the unitary-five full block coordinates

The unipotent radical and the cubic torus preserve the chosen plane. For their
product with the middle SU₃, plane stabilization is therefore exactly
stabilization of the middle line `(a,a,0)`. The projective scalar kernel fixes
every subspace, so this equivalence holds in the actual projective parabolic.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

theorem leviMatrix_mulVec (A : Matrix (Fin 3) (Fin 3) F) (w : Fin 5 → F) :
    leviMatrix A *ᵥ w =
      ![w 0, w 1, (A *ᵥ ![w 2,w 3,w 4]) 0,
        (A *ᵥ ![w 2,w 3,w 4]) 1, (A *ᵥ ![w 2,w 3,w 4]) 2] := by
  ext i
  fin_cases i <;> simp [leviMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem leviSU_mem_plane_iff (hJ : J.form = 1) (A : (middleForm J).specialSubgroup) :
    leviSU J hJ A ∈ specialStabilizer J (plane F) ↔
      ∀ v : Fin 3 → F,
        ((A.val.val *ᵥ v) 1 = (A.val.val *ᵥ v) 0 ∧ (A.val.val *ᵥ v) 2 = 0) ↔
          (v 1 = v 0 ∧ v 2 = 0) := by
  rw [mem_specialStabilizer_iff]
  change (∀ w : Fin 5 → F, leviMatrix A.val.val *ᵥ w ∈ plane F ↔ w ∈ plane F) ↔ _
  simp only [leviMatrix_mulVec]
  constructor
  · intro h v
    have hv : ![v 0,v 1,v 2] = v := by ext i; fin_cases i <;> rfl
    simpa [plane, hv] using h ![0,0,v 0,v 1,v 2]
  · intro h w
    have hv := h ![w 2,w 3,w 4]
    change (w 1 = w 0 ∧
      (A.val.val *ᵥ ![w 2,w 3,w 4]) 1 = (A.val.val *ᵥ ![w 2,w 3,w 4]) 0 ∧
        (A.val.val *ᵥ ![w 2,w 3,w 4]) 2 = 0) ↔
      (w 1 = w 0 ∧ w 3 = w 2 ∧ w 4 = 0)
    exact and_congr_right (fun _ => hv)

/-- Scalar projectivization does not alter subspace stabilization. -/
theorem project_mem_parabolic_iff (W : Submodule F (Fin 5 → F)) (A : J.specialSubgroup) :
    project J A ∈ parabolic J W ↔ A ∈ specialStabilizer J W := by
  have he := Subgroup.comap_map_eq_self (ker_project_le_specialStabilizer J W)
  exact Iff.of_eq (congrArg (fun H : Subgroup J.specialSubgroup => A ∈ H) he)

theorem leviParabolic_mem_overlap_iff (hJ : J.form = 1)
    (A : (middleForm J).specialSubgroup) :
    leviParabolic J hJ A ∈ (lineParabolic J ⊓ planeParabolic J).subgroupOf (lineParabolic J) ↔
      ∀ v : Fin 3 → F,
        ((A.val.val *ᵥ v) 1 = (A.val.val *ᵥ v) 0 ∧ (A.val.val *ᵥ v) 2 = 0) ↔
          (v 1 = v 0 ∧ v 2 = 0) := by
  change ((leviParabolic J hJ A).val ∈ lineParabolic J ∧
    project J (leviSU J hJ A) ∈ planeParabolic J) ↔ _
  rw [and_iff_right (leviParabolic J hJ A).property]
  exact (project_mem_parabolic_iff J (plane F) _).trans (leviSU_mem_plane_iff J hJ A)

variable [CharP F 2] (hconj : ∀ x, J.conj x = x ^ 4)

/-- The exact flag criterion for every concrete full-product matrix. -/
theorem fullMap_mem_overlap_iff (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (x : FullProduct J hconj) :
    fullMap J hconj c hc hJ x ∈
        (lineParabolic J ⊓ planeParabolic J).subgroupOf (lineParabolic J) ↔
      ∀ v : Fin 3 → F,
        ((x.right.1.val.val *ᵥ v) 1 = (x.right.1.val.val *ᵥ v) 0 ∧
          (x.right.1.val.val *ᵥ v) 2 = 0) ↔ (v 1 = v 0 ∧ v 2 = 0) := by
  let H := (lineParabolic J ⊓ planeParabolic J).subgroupOf (lineParabolic J)
  have hu : toParabolic J hJ x.left ∈ H :=
    projectiveUnipotent_le_overlap J hJ ⟨x.left, rfl⟩
  have hb : cubicParabolic J hconj c hc hJ x.right.2 ∈ H :=
    cubicParabolic_mem_overlap J hconj c hc hJ x.right.2
  have he : fullMap J hconj c hc hJ x ∈ H ↔ leviParabolic J hJ x.right.1 ∈ H := by
    rw [fullMap_apply]
    exact (H.mul_mem_cancel_left hu).trans (H.mul_mem_cancel_right hb)
  exact he.trans (leviParabolic_mem_overlap_iff J hJ x.right.1)

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks
