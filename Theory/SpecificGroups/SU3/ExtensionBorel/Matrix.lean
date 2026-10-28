module
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.DiagonalActors
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Triangular unitary matrices and the root stabilizer

Upper triangular unitary matrices conjugate the Hermitian Heisenberg root
matrices to root matrices: the conjugate remains triangular with diagonal one,
and the unitary equation recovers its two root coordinates. Together with the
projective intertwining calculation this gives both directions of the root
stabilizer test for a concrete semilinear representative.

Source: Huppert II.10.12; Aschbacher–Smith, Notation A.3.16, Lemma A.3.18,
printed pp.51–52, and the Borel placement in 13.6.6, printed p.927.
-/

@[expose] public section
open Matrix BenderSuzuki.External Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel
open BorelTorus BorelTorus.SemilinearActors
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Upper triangular matrices inside the actual unitary group. -/
def upperUnitary : Subgroup J.unitarySubgroup where
  carrier := {u | u.val.val.IsUpperTriangular}
  one_mem' := by intro i j hij; exact Matrix.one_apply_ne (ne_of_gt hij)
  mul_mem' := fun hu hv => hu.mul hv
  inv_mem' := by
    intro u hu
    change (u.val⁻¹).val.IsUpperTriangular
    simpa only [GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hu

private theorem upper_of_entries (M : Matrix (Fin 3) (Fin 3) E)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h21 : M 2 1 = 0) :
    M.IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem upper_mul_diag {M N : Matrix (Fin 3) (Fin 3) E}
    (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) (i : Fin 3) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

variable [Finite E]

private theorem unitriangular_eq_root
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (v : J.unitarySubgroup) (hv : v ∈ upperUnitary J)
    (hd : ∀ i, v.val.val i i = 1) :
    ∃ z : hermitianUnipotentCoord J, v.val = hermitianUnipotentGL J z := by
  obtain ⟨z, d, hf, hdiag, _⟩ := upper_unitary_factorization J hJ v
    (hv (by decide)) (hv (by decide)) (hv (by decide))
  have hd1 : d = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst j
      have he := congrArg (fun g : GL (Fin 3) E => g.val i i) hf
      have hz : (hermitianUnipotentGL J z).val.IsUpperTriangular := by
        apply upper_of_entries <;> simp [hermitianUnipotentMatrix]
      have hdu : d.val.val.IsUpperTriangular := fun _ _ h => hdiag _ _ (ne_of_gt h)
      change v.val.val i i = ((hermitianUnipotentGL J z).val * d.val.val) i i at he
      rw [upper_mul_diag hz hdu, hd] at he
      have hz1 : (hermitianUnipotentGL J z).val i i = 1 := by fin_cases i <;> rfl
      change d.val.val i i = (1 : Matrix (Fin 3) (Fin 3) E) i i
      rw [Matrix.one_apply_eq]
      simpa only [hz1, one_mul] using he.symm
    · change d.val.val i j = (1 : Matrix (Fin 3) (Fin 3) E) i j
      simpa only [Matrix.one_apply_ne hij] using hdiag i j hij
  exact ⟨z, by simpa only [hd1, Subgroup.coe_one, mul_one] using hf⟩

/-- Triangular unitary conjugation preserves the actual root matrices. -/
theorem upper_conjugates_root
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (u : J.unitarySubgroup) (hu : u ∈ upperUnitary J)
    (z : hermitianUnipotentCoord J) :
    ∃ w : hermitianUnipotentCoord J,
      u.val * hermitianUnipotentGL J z * u.val⁻¹ = hermitianUnipotentGL J w := by
  let r : J.unitarySubgroup := ⟨hermitianUnipotentGL J z,
    (hermitianUnipotentSU J hJ z).property.1⟩
  have hr : r ∈ upperUnitary J := by
    apply upper_of_entries <;> simp [r, hermitianUnipotentMatrix]
  have hui := (upperUnitary J).inv_mem hu
  apply unitriangular_eq_root J hJ (u * r * u⁻¹)
    ((upperUnitary J).mul_mem ((upperUnitary J).mul_mem hu hr) hui)
  intro i
  have h1 : u.val.val i i * (u⁻¹).val.val i i = 1 := by
    rw [← upper_mul_diag hu hui]
    change (u * u⁻¹).val.val i i = 1
    simp
  change ((u.val.val * r.val.val) * (u⁻¹).val.val) i i = 1
  rw [upper_mul_diag (hu.mul hr) hui, upper_mul_diag hu hr]
  have hr1 : r.val.val i i = 1 := by fin_cases i <;> rfl
  rw [hr1, mul_one, h1]

private instance : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

/-- The converse triangular calculation, including entrywise field action. -/
theorem root_map_eq_of_upper_formula
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (u : J.unitarySubgroup) (hupper : u ∈ upperUnitary J)
    (hu : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk u.val *
        ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk u.val)⁻¹) :
    (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, ⟨z, rfl⟩, rfl⟩
    obtain ⟨w, hw⟩ := upper_conjugates_root J hJ u hupper (rootFieldEquiv J σ z)
    refine ⟨w, Subtype.ext ?_⟩
    change ProjGenLinGroup.mk (hermitianUnipotentGL J w) =
      (a (hermitianUnipotentPSU J hJ z)).val
    rw [hu]
    change _ = ProjGenLinGroup.mk u.val *
      ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.mk (hermitianUnipotentGL J z)) * _
    rw [ProjGenLinGroup.map_mk, field_map_root]
    simpa only [map_mul, map_inv] using congrArg ProjGenLinGroup.mk hw.symm
  · exact le_of_eq (Subgroup.card_map_of_injective a.injective).symm

/-- Exact root-stabilizer test for any given semilinear matrix representative. -/
theorem root_map_eq_iff_upper
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (u : J.unitarySubgroup)
    (hu : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk u.val *
        ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk u.val)⁻¹) :
    (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ ↔
      u ∈ upperUnitary J := by
  constructor
  · intro hr
    obtain ⟨h10, h20, h21⟩ := projective_semilinear_upper J hJ hcard hfixed a σ u hu hr
    exact upper_of_entries _ h10 h20 h21
  · exact fun h => root_map_eq_of_upper_formula J hJ a σ u h hu

end BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel
