module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.LineCenter

/-!
# Full native long-root centralizers in PSU₅(4)

A nonidentity central element of the line radical is a rank-one transvection.
Commutation with its matrix forces preservation of its image, the chosen
isotropic line. Projective commutation lifts using the actual scalar kernel
of order five and the radical's fourth-power relation. Thus its centralizer
in the entire projective group lies in the line parabolic.

The ChapterF companion applies this to the model's literal long-root center
and its full extensions. Source: Aschbacher–Smith F.4.27(4), printed p.288.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive
open LineCore LineCore.Parabolic
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem preserves_line (J : HermitianForm 5 F)
    (u : Coord J) (hu : u.vector = 0) (hb : u.scalar ≠ 0)
    (B : Matrix (Fin 5) (Fin 5) F)
    (hB : B * ambientMatrix J u = ambientMatrix J u * B)
    (v : Fin 5 → F) (hv : v ∈ line F) : B *ᵥ v ∈ line F := by
  have he (i j : Fin 5) := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j) hB
  have h01 : B 0 1 = B 1 0 := by
    apply mul_left_cancel₀ hb
    have h := he 0 0
    simp [ambientMatrix,hu,Matrix.mul_apply,Fin.sum_univ_succ] at h
    linear_combination h
  have h11 : B 1 1 = B 0 0 := by
    apply mul_left_cancel₀ hb
    have h := he 1 0
    simp [ambientMatrix,hu,Matrix.mul_apply,Fin.sum_univ_succ] at h
    linear_combination h
  have hs (i : Fin 5) (hi : i ≠ 0) (hj : i ≠ 1) : B i 0 + B i 1 = 0 := by
    apply mul_left_cancel₀ hb
    have h := he i 0
    fin_cases i
    · exact (hi rfl).elim
    · exact (hj rfl).elim
    · change u.scalar * (B 2 0 + B 2 1) = u.scalar * 0
      simp [ambientMatrix,hu,Matrix.mul_apply,Fin.sum_univ_succ] at h
      linear_combination h
    · change u.scalar * (B 3 0 + B 3 1) = u.scalar * 0
      simp [ambientMatrix,hu,Matrix.mul_apply,Fin.sum_univ_succ] at h
      linear_combination h
    · change u.scalar * (B 4 0 + B 4 1) = u.scalar * 0
      simp [ambientMatrix,hu,Matrix.mul_apply,Fin.sum_univ_succ] at h
      linear_combination h
  change v 1 = v 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 at hv
  change _ = _ ∧ _ = 0 ∧ _ = 0 ∧ _ = 0
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv.1,hv.2.1,hv.2.2.1,
    hv.2.2.2,mul_zero,add_zero,h01,h11]
  constructor
  · ring
  · exact ⟨by linear_combination v 0 * hs 2 (by decide) (by decide),
      by linear_combination v 0 * hs 3 (by decide) (by decide),
      by linear_combination v 0 * hs 4 (by decide) (by decide)⟩

/-- The full projective centralizer of a nonidentity long-root element lies
in its native line parabolic. -/
theorem long_root_centralizer_le [Finite F] (J : HermitianForm 5 F)
    (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x ^ 4) (hcard : Nat.card F = 16)
    (c : F) (hc : c + J.conj c = 1)
    (u : Coord J) (hu : u ∈ center (Coord J)) (hune : u ≠ 1) :
    centralizer ({(toParabolic J hJ u).val} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      lineParabolic J := by
  have hv : u.vector = 0 := (Coord.mem_center_iff_vector_eq_zero c hc u).mp hu
  have hb : u.scalar ≠ 0 := fun he => hune (Coord.ext hv he)
  intro g hg
  obtain ⟨A,rfl⟩ := project_surjective J g
  have hcomm : A * toSU J hJ u = toSU J hJ u * A :=
    RadicalCentralizers.commute_of_project_commute_fourth_power J hconj hcard
      (mem_centralizer_singleton_iff.mp hg)
      (by rw [←map_pow,Coord.fourth_power,map_one])
  have hm (B : J.specialSubgroup) (hB : B * toSU J hJ u = toSU J hJ u * B)
      (v : Fin 5 → F) (hv' : v ∈ line F) : linearAction J B v ∈ line F := by
    apply preserves_line J u hv hb B.val.val _ v hv'
    have hh := congrArg (fun X : J.specialSubgroup => X.val.val) hB
    change B.val.val * (ambientGL J u).val = (ambientGL J u).val * B.val.val at hh
    rwa [ambientGL_val] at hh
  refine ⟨A,?_,rfl⟩
  apply (mem_specialStabilizer_iff J (line F) A).mpr
  intro v
  constructor
  · intro h
    have hh := hm A⁻¹ (show Commute A⁻¹ (toSU J hJ u) from
      (show Commute A (toSU J hJ u) from hcomm).inv_left) _ h
    change linearAction J A⁻¹ (linearAction J A v) ∈ line F at hh
    have hi : linearAction J A⁻¹ (linearAction J A v) = v := by
      rw [map_inv]
      exact (linearAction J A).symm_apply_apply v
    exact hi ▸ hh
  · exact hm A hcomm v

end Theory.SpecificGroups.UnitaryFive
