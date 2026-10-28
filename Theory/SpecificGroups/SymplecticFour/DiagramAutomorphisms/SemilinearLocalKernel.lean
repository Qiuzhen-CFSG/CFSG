module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel.Parabolics
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Two-element kernels of the explicit semilinear local actions

For an automorphism `conj g * fieldAutomorphism σ` preserving either local
factor, the linear part belongs to the corresponding full parabolic. The
quotient conjugation formulas include its scalar torus. Companion-matrix
traces force `σ = 1` if the actual local SL₂ action is trivial. The center of
Sp₄ is trivial in characteristic two, so a two-power order inner automorphism
comes from a two-power order matrix. Its determinant character is one, since
squaring is injective in the field. Thus its conjugating matrix belongs to the
local determinant kernel.

These statements use explicitly semilinear automorphisms; they do not require
or assume a classification of automorphisms. They supply the local detection
step for Aschbacher--Smith F.1.12, printed p.264 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

/-- The exact point quotient action of an explicitly semilinear automorphism. -/
theorem pointSL2Action_semilinear (g : Sp F) (σ : F ≃+* F)
    (hL : pointLocal.map ((MulAut.conj g) * fieldAutomorphism σ).toMonoidHom = pointLocal)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    pointSL2Action hcard hn ((MulAut.conj g) * fieldAutomorphism σ) hL A =
      pointParabolicQuotient ⟨g, point_semilinear_mem_parabolic hcard hn g σ hL⟩ *
        Matrix.SpecialLinearGroup.map σ.toRingHom A *
      (pointParabolicQuotient ⟨g, point_semilinear_mem_parabolic hcard hn g σ hL⟩)⁻¹ := by
  obtain ⟨l, rfl⟩ := pointQuotient_surjective A
  rw [pointSL2Action_quotient]
  let l' := restrict (fieldAutomorphism σ) pointLocal
    (pointLocal_map hcard hn _ (field_map_pointParabolic σ)) l
  have hl : g * l'.val * g⁻¹ ∈ pointLocal :=
    (restrict ((MulAut.conj g) * fieldAutomorphism σ) pointLocal hL l).property
  change pointQuotient ⟨g * l'.val * g⁻¹, hl⟩ = _
  rw [pointQuotient_conjugate
    ⟨g, point_semilinear_mem_parabolic hcard hn g σ hL⟩ l' hl]
  rfl

/-- The exact plane quotient action, retaining its full GL₂ conjugating matrix. -/
theorem planeSL2Action_semilinear (g : Sp F) (σ : F ≃+* F)
    (hL : planeLocal.map ((MulAut.conj g) * fieldAutomorphism σ).toMonoidHom = planeLocal)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (planeSL2Action hcard hn ((MulAut.conj g) * fieldAutomorphism σ) hL A).val =
      Plane.upperLeft ⟨g, plane_semilinear_mem_parabolic hcard hn g σ hL⟩ *
        (Matrix.SpecialLinearGroup.map σ.toRingHom A).val *
      Plane.upperLeft (⟨g, plane_semilinear_mem_parabolic hcard hn g σ hL⟩ : planeParabolic)⁻¹ := by
  obtain ⟨l, rfl⟩ := Plane.quotientMap_surjective A
  rw [planeSL2Action_quotient]
  let l' := restrict (fieldAutomorphism σ) planeLocal
    (planeLocal_map hcard hn _ (field_map_planeParabolic σ)) l
  have hl : g * l'.val * g⁻¹ ∈ planeLocal :=
    (restrict ((MulAut.conj g) * fieldAutomorphism σ) planeLocal hL l).property
  change (Plane.quotientMap ⟨g * l'.val * g⁻¹, hl⟩).val = _
  rw [planeQuotient_conjugate
    ⟨g, plane_semilinear_mem_parabolic hcard hn g σ hL⟩ l' hl]
  rfl

/-- A trivial point-local action eliminates the semilinear field contribution. -/
theorem pointSL2Action_semilinear_field_eq_refl (g : Sp F) (σ : F ≃+* F)
    (hL : pointLocal.map ((MulAut.conj g) * fieldAutomorphism σ).toMonoidHom = pointLocal)
    (hact : pointSL2Action hcard hn ((MulAut.conj g) * fieldAutomorphism σ) hL = 1) :
    σ = RingEquiv.refl F := by
  let c := pointParabolicQuotient ⟨g, point_semilinear_mem_parabolic hcard hn g σ hL⟩
  apply fieldEquiv_eq_refl_of_SL2_inner σ c⁻¹
  intro A
  have h := congrArg (fun a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => a A) hact
  rw [pointSL2Action_semilinear] at h
  change c * Matrix.SpecialLinearGroup.map σ.toRingHom A * c⁻¹ = A at h
  calc
    _ = c⁻¹ * (c * Matrix.SpecialLinearGroup.map σ.toRingHom A * c⁻¹) * c := by
      simp [mul_assoc]
    _ = c⁻¹ * A * (c⁻¹)⁻¹ := by rw [h, inv_inv]

omit [Finite F] [CharP F 2] in
private theorem field_eq_refl_of_matrix_conjugate (σ : F ≃+* F)
    (C D : Matrix (Fin 2) (Fin 2) F) (hDC : D * C = 1)
    (h : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      C * (Matrix.SpecialLinearGroup.map σ.toRingHom A).val * D = A.val) :
    σ = RingEquiv.refl F := by
  apply RingEquiv.ext
  intro t
  let A : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have he := congrArg Matrix.trace (h A)
  rw [Matrix.trace_mul_cycle, hDC, Matrix.one_mul] at he
  change Matrix.trace (A.val.map σ) = Matrix.trace A.val at he
  simpa [A, Matrix.trace, Fin.sum_univ_two] using he

/-- A trivial plane-local action eliminates the field contribution, including in the presence of scalars. -/
theorem planeSL2Action_semilinear_field_eq_refl (g : Sp F) (σ : F ≃+* F)
    (hL : planeLocal.map ((MulAut.conj g) * fieldAutomorphism σ).toMonoidHom = planeLocal)
    (hact : planeSL2Action hcard hn ((MulAut.conj g) * fieldAutomorphism σ) hL = 1) :
    σ = RingEquiv.refl F := by
  let gp : planeParabolic (F := F) := ⟨g, plane_semilinear_mem_parabolic hcard hn g σ hL⟩
  apply field_eq_refl_of_matrix_conjugate σ (Plane.upperLeft gp) (Plane.upperLeft gp⁻¹)
  · rw [← map_mul, inv_mul_cancel, map_one]
  · intro A
    have h := congrArg (fun a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => (a A).val) hact
    rw [planeSL2Action_semilinear] at h
    exact h

omit [Finite F] in
private theorem eq_one_of_pow_two_pow (x : F) (k : ℕ) (h : x ^ (2 ^ k) = 1) : x = 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    rw [pow_succ, pow_mul] at h
    exact CharTwo.sq_injective (by simpa using h)

omit [Finite F] in
private theorem inner_twoPower_mem_determinantKernel (W : Submodule F (Vector F))
    (g : Sp F) (hg : g ∈ stabilizer W)
    (htwo : ∃ k : ℕ, (MulAut.conj g) ^ (2 ^ k) = 1) : g ∈ determinantKernel W := by
  obtain ⟨k, hk⟩ := htwo
  have hconj : MulAut.conj (g ^ (2 ^ k)) = 1 := by rw [map_pow]; exact hk
  have hc : g ^ (2 ^ k) ∈ Subgroup.center (Sp F) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun a : MulAut (Sp F) => a x) hconj
    change g ^ (2 ^ k) * x * (g ^ (2 ^ k))⁻¹ = x at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hp : g ^ (2 ^ k) = 1 := by
    simpa only [EvenProjective.center_eq_bot, Subgroup.mem_bot] using hc
  have hgp : (⟨g, hg⟩ : stabilizer W) ^ (2 ^ k) = 1 := Subtype.ext hp
  have hχ := congrArg (fun x : stabilizer W => (determinantCharacter W x : F)) hgp
  simp only [map_pow, Units.val_pow_eq_pow_val, map_one, Units.val_one] at hχ
  exact ⟨⟨g, hg⟩, Units.ext (eq_one_of_pow_two_pow _ k hχ), rfl⟩

omit [Finite F] [CharP F 2] in
private theorem fieldAutomorphism_refl : fieldAutomorphism (RingEquiv.refl F) = 1 := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rfl

/-- Every two-element in the explicit semilinear point-action kernel is induced by a point-local element. -/
theorem pointSL2Action_semilinear_kernel (g : Sp F) (σ : F ≃+* F)
    (hL : pointLocal.map ((MulAut.conj g) * fieldAutomorphism σ).toMonoidHom = pointLocal)
    (htwo : ∃ k : ℕ, ((MulAut.conj g) * fieldAutomorphism σ) ^ (2 ^ k) = 1)
    (hact : pointSL2Action hcard hn ((MulAut.conj g) * fieldAutomorphism σ) hL = 1) :
    ∃ l : pointLocal (F := F),
      (MulAut.conj g) * fieldAutomorphism σ = MulAut.conj l.val := by
  have hσ := pointSL2Action_semilinear_field_eq_refl hcard hn g σ hL hact
  have ha : (MulAut.conj g) * fieldAutomorphism σ = MulAut.conj g := by
    rw [hσ, fieldAutomorphism_refl, mul_one]
  have hg := point_semilinear_mem_parabolic hcard hn g σ hL
  rw [ha] at htwo
  exact ⟨⟨g, inner_twoPower_mem_determinantKernel (point F) g hg htwo⟩, ha⟩

/-- Every two-element in the explicit semilinear plane-action kernel is induced by a plane-local element. -/
theorem planeSL2Action_semilinear_kernel (g : Sp F) (σ : F ≃+* F)
    (hL : planeLocal.map ((MulAut.conj g) * fieldAutomorphism σ).toMonoidHom = planeLocal)
    (htwo : ∃ k : ℕ, ((MulAut.conj g) * fieldAutomorphism σ) ^ (2 ^ k) = 1)
    (hact : planeSL2Action hcard hn ((MulAut.conj g) * fieldAutomorphism σ) hL = 1) :
    ∃ l : planeLocal (F := F),
      (MulAut.conj g) * fieldAutomorphism σ = MulAut.conj l.val := by
  have hσ := planeSL2Action_semilinear_field_eq_refl hcard hn g σ hL hact
  have ha : (MulAut.conj g) * fieldAutomorphism σ = MulAut.conj g := by
    rw [hσ, fieldAutomorphism_refl, mul_one]
  have hg := plane_semilinear_mem_parabolic hcard hn g σ hL
  rw [ha] at htwo
  exact ⟨⟨g, inner_twoPower_mem_determinantKernel (plane F) g hg htwo⟩, ha⟩

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
