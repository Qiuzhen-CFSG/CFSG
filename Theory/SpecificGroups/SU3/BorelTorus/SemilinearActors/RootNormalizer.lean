module

public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.Coordinates

/-!
# A root-normalizing semilinear representative is triangular

A root element with first coordinate one forces the first column of an
intertwining matrix to be supported on the first coordinate, even when
the intertwining equality is only projective. The unitary equation then
kills the remaining entry below the diagonal. Root preservation by an
arbitrary semilinear actor supplies precisely this intertwining equation.
No torus preservation or condition on the actor's involution powers is used.

Source: the root matrices of Huppert II.10.12 and the unitary semilinear
calculation in Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

public section

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

theorem unitary_upper_of_root_intertwining
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (u : J.unitarySubgroup)
    (hu : ∀ t : hermitianUnipotentCoord J, ∃ z : hermitianUnipotentCoord J,
      ProjGenLinGroup.mk (u.val * hermitianUnipotentGL J z) =
        ProjGenLinGroup.mk (hermitianUnipotentGL J t * u.val)) :
    u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 ∧ u.val.val 2 1 = 0 := by
  obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed (-1) (by simp)
  let t : hermitianUnipotentCoord J := ⟨(1, b), by
    dsimp only
    rw [map_one, mul_one, hb, neg_add_cancel]⟩
  have ht' : t.val.1 = 1 := rfl
  obtain ⟨z, hz⟩ := hu t
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hz
  have h0 := congrArg (fun M : GL (Fin 3) E => M.val 0 0) hc
  have h1 := congrArg (fun M : GL (Fin 3) E => M.val 1 0) hc
  have h2 := congrArg (fun M : GL (Fin 3) E => M.val 2 0) hc
  simp [GeneralLinearGroup.coe_scalar, hermitianUnipotentMatrix,
    Matrix.mul_apply, Fin.sum_univ_three, ht'] at h0 h1 h2
  have hcol : u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 := by
    by_cases hc1 : (c : E) = 1
    · rw [hc1, mul_one] at h0 h1
      have h20 : u.val.val 2 0 = 0 := by linear_combination h1
      refine ⟨?_, h20⟩
      rw [h20] at h0
      linear_combination -h0
    · have h20 : u.val.val 2 0 = 0 := by
        exact (mul_eq_zero.mp (show u.val.val 2 0 * ((c : E) - 1) = 0 by
          linear_combination h2)).resolve_right (sub_ne_zero.mpr hc1)
      refine ⟨?_, h20⟩
      exact (mul_eq_zero.mp (show u.val.val 1 0 * ((c : E) - 1) = 0 by
        rw [h20] at h1
        linear_combination h1)).resolve_right (sub_ne_zero.mpr hc1)
  obtain ⟨h10, h20⟩ := hcol
  refine ⟨h10, h20, ?_⟩
  have hunit := (J.mem_unitarySubgroup_iff _).mp u.property
  rw [hJ] at hunit
  have h01 := congrArg (fun X : Matrix (Fin 3) (Fin 3) E => X 0 1) hunit
  have h02 := congrArg (fun X : Matrix (Fin 3) (Fin 3) E => X 0 2) hunit
  have hnonzero : J.conj (u.val.val 0 0) ≠ 0 := by
    apply left_ne_zero_of_mul_eq_one (b := u.val.val 2 2)
    simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
      h10, h20] using h02
  apply (mul_eq_zero.mp ?_).resolve_left hnonzero
  simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
    h10, h20] using h01

theorem special_semilinear_upper
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (a : MulAut J.specialSubgroup) (σ : E ≃+* E) (u : J.unitarySubgroup)
    (hu : ∀ x : J.specialSubgroup,
      (a x).val = u.val * GeneralLinearGroup.map σ.toRingHom x.val * u.val⁻¹)
    (hroot : (specialRoot J hJ).map a.toMonoidHom = specialRoot J hJ) :
    u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 ∧ u.val.val 2 1 = 0 := by
  apply unitary_upper_of_root_intertwining J hJ hcard hfixed u
  intro t
  have ht : hermitianUnipotentSU J hJ t ∈ (specialRoot J hJ).map a.toMonoidHom := by
    rw [hroot]
    exact ⟨t, rfl⟩
  obtain ⟨x, ⟨z, rfl⟩, hx⟩ := ht
  refine ⟨rootFieldEquiv J σ z, ?_⟩
  have he := congrArg Subtype.val hx
  change (a (hermitianUnipotentSU J hJ z)).val = (hermitianUnipotentSU J hJ t).val at he
  rw [hu] at he
  change u.val * GeneralLinearGroup.map σ.toRingHom (hermitianUnipotentGL J z) *
    u.val⁻¹ = hermitianUnipotentGL J t at he
  rw [field_map_root] at he
  exact congrArg ProjGenLinGroup.mk (mul_inv_eq_iff_eq_mul.mp he)

theorem projective_semilinear_upper
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (u : J.unitarySubgroup)
    (hu : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk u.val *
        ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk u.val)⁻¹)
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ) :
    u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 ∧ u.val.val 2 1 = 0 := by
  apply unitary_upper_of_root_intertwining J hJ hcard hfixed u
  intro t
  have ht : hermitianUnipotentPSU J hJ t ∈ (projectiveRoot J hJ).map a.toMonoidHom := by
    rw [hroot]
    exact ⟨t, rfl⟩
  obtain ⟨x, ⟨z, rfl⟩, hx⟩ := ht
  refine ⟨rootFieldEquiv J σ z, ?_⟩
  have he := congrArg Subtype.val hx
  change (a (hermitianUnipotentPSU J hJ z)).val = (hermitianUnipotentPSU J hJ t).val at he
  rw [hu] at he
  change ProjGenLinGroup.mk u.val *
    ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.mk (hermitianUnipotentGL J z)) *
    (ProjGenLinGroup.mk u.val)⁻¹ = ProjGenLinGroup.mk (hermitianUnipotentGL J t) at he
  rw [ProjGenLinGroup.map_mk, field_map_root] at he
  simpa only [map_mul] using mul_inv_eq_iff_eq_mul.mp he

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors
