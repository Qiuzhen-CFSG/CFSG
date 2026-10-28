module

public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.Coordinates
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Full torus action of triangular unitary semilinear representatives

Conjugation by an upper triangular unitary matrix changes each full diagonal
torus element by a root element. Indeed the matrix commutator is upper
triangular with diagonal entries one, and the unitary equation gives exactly
the Hermitian Heisenberg root coordinates. Combining this calculation with
entrywise field action proves the torus displacement formulas in both SU₃
and its actual projective image.

The root and torus intersect trivially in each carrier. In the projective
calculation the scalar relating matrix representatives is kept, so fixation
modulo the root means equality of projective torus elements, retaining the
cubic kernel of the full torus parametrization. No torus preservation or
induced quotient action is assumed.

Source: Huppert II.10.12 for the matrix coordinates; the unitary automorphism
calculation in Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
The numerical restrictions in that application are unnecessary here, apart
from finiteness ensuring that field automorphisms commute with the involution.
-/

public section

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private theorem upper_of_entries (M : Matrix (Fin 3) (Fin 3) E)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h21 : M 2 1 = 0) :
    M.IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem upper_inv (g : GL (Fin 3) E) (h : g.val.IsUpperTriangular) :
    (g⁻¹).val.IsUpperTriangular := by
  simpa only [GeneralLinearGroup.coe_inv] using
    (Matrix.blockTriangular_inv_of_blockTriangular h)

private theorem upper_mul_diag {M N : Matrix (Fin 3) (Fin 3) E}
    (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) (i : Fin 3) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

private theorem upper_commutator (g t : GL (Fin 3) E)
    (hg : g.val.IsUpperTriangular) (ht : t.val.IsUpperTriangular) :
    (g * t * g⁻¹ * t⁻¹).val.IsUpperTriangular ∧
      ∀ i, (g * t * g⁻¹ * t⁻¹).val i i = 1 := by
  have hgi := upper_inv g hg
  have hti := upper_inv t ht
  refine ⟨((hg.mul ht).mul hgi).mul hti, fun i => ?_⟩
  have hg1 : g.val i i * (g⁻¹).val i i = 1 := by
    rw [← upper_mul_diag hg hgi]
    change (g * g⁻¹).val i i = 1
    simp
  have ht1 : t.val i i * (t⁻¹).val i i = 1 := by
    rw [← upper_mul_diag ht hti]
    change (t * t⁻¹).val i i = 1
    simp
  change (((g.val * t.val) * (g⁻¹).val) * (t⁻¹).val) i i = 1
  rw [upper_mul_diag ((hg.mul ht).mul hgi) hti,
    upper_mul_diag (hg.mul ht) hgi, upper_mul_diag hg ht]
  calc
    _ = (g.val i i * (g⁻¹).val i i) * (t.val i i * (t⁻¹).val i i) := by ring
    _ = 1 := by rw [hg1, ht1, one_mul]

private theorem unitriangular_eq_root
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (v : J.unitarySubgroup) (hv : v.val.val.IsUpperTriangular)
    (hd : ∀ i, v.val.val i i = 1) :
    ∃ z : hermitianUnipotentCoord J, v.val = hermitianUnipotentGL J z := by
  have h10 : v.val.val 1 0 = 0 := hv (by decide)
  have h20 : v.val.val 2 0 = 0 := hv (by decide)
  have h21 : v.val.val 2 1 = 0 := hv (by decide)
  have hu := (J.mem_unitarySubgroup_iff _).mp v.property
  rw [hJ] at hu
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 2) hu
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hu
  simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
    h21, hd] at h12 h22
  have he : v.val.val 1 2 = -J.conj (v.val.val 0 1) := by linear_combination h12
  have hz : v.val.val 0 2 + J.conj (v.val.val 0 2) +
      v.val.val 0 1 * J.conj (v.val.val 0 1) = 0 := by
    rw [he, map_neg, J.conj_involutive] at h22
    linear_combination h22
  refine ⟨⟨(v.val.val 0 1, v.val.val 0 2), hz⟩, ?_⟩
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentMatrix, hd, h10, h20, h21, he]

/-- A triangular unitary representative has root-valued displacement on every
member of the full diagonal torus. -/
theorem unitary_upper_torus_displacement
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (u : J.unitarySubgroup)
    (h10 : u.val.val 1 0 = 0) (h20 : u.val.val 2 0 = 0)
    (h21 : u.val.val 2 1 = 0) (k : Eˣ) :
    ∃ z : hermitianUnipotentCoord J,
      u.val * hermitianTorusGL J k * u.val⁻¹ * (hermitianTorusGL J k)⁻¹ =
        hermitianUnipotentGL J z := by
  let t : J.unitarySubgroup := ⟨hermitianTorusGL J k,
    J.specialSubgroup_le_unitarySubgroup (hermitianTorusSU J hJ k).property⟩
  have ht : t.val.val.IsUpperTriangular := by
    apply upper_of_entries <;> simp [t, hermitianTorusMatrix]
  obtain ⟨hv, hd⟩ := upper_commutator u.val t.val
    (upper_of_entries _ h10 h20 h21) ht
  exact unitriangular_eq_root J hJ (u * t * u⁻¹ * t⁻¹) hv hd

/-- The special root and full special torus meet trivially. -/
theorem special_torus_mem_root_iff
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Eˣ) :
    hermitianTorusSU J hJ k ∈ specialRoot J hJ ↔ hermitianTorusSU J hJ k = 1 := by
  constructor
  · rintro ⟨z, hz⟩
    have he := congrArg (fun x : J.specialSubgroup => x.val.val 2 2) hz
    have hk : k = 1 := Units.ext he.symm
    simp [hk]
  · rintro h
    rw [h]
    exact (specialRoot J hJ).one_mem

/-- The projective root and full projective torus meet trivially; the scalar
in a projective matrix equality is retained in the calculation. -/
theorem projective_torus_mem_root_iff
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Eˣ) :
    hermitianTorusPSU J hJ k ∈ projectiveRoot J hJ ↔ hermitianTorusPSU J hJ k = 1 := by
  constructor
  · rintro ⟨z, hz⟩
    have hp : ProjGenLinGroup.mk (hermitianUnipotentGL J z) =
        ProjGenLinGroup.mk (hermitianTorusGL J k) := congrArg Subtype.val hz
    obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
    have h01 := congrArg (fun g : GL (Fin 3) E => g.val 0 1) hc
    have h02 := congrArg (fun g : GL (Fin 3) E => g.val 0 2) hc
    simp [GeneralLinearGroup.coe_scalar, hermitianUnipotentMatrix,
      hermitianTorusMatrix, Matrix.mul_apply, Fin.sum_univ_three] at h01 h02
    have hz0 : z = 1 := by
      apply Subtype.ext
      apply Prod.ext
      · exact h01
      · exact h02
    simpa only [hz0, map_one] using hz.symm
  · rintro h
    rw [h]
    exact (projectiveRoot J hJ).one_mem

/-- Disjointness is for the actual special matrix subgroups. -/
theorem special_root_disjoint_torus
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Disjoint (specialRoot J hJ) (specialTorus J hJ) := by
  apply Subgroup.disjoint_def.mpr
  rintro x hx ⟨k, rfl⟩
  exact (special_torus_mem_root_iff J hJ k).mp hx

/-- Disjointness is for the actual projective subgroups, without making the
full torus parametrization injective. -/
theorem projective_root_disjoint_torus
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Disjoint (projectiveRoot J hJ) (projectiveTorus J hJ) := by
  apply Subgroup.disjoint_def.mpr
  rintro x hx ⟨k, rfl⟩
  exact (projective_torus_mem_root_iff J hJ k).mp hx

variable [Finite E]

/-- Every special-unitary semilinear actor with triangular unitary part acts
on the full torus modulo the root by its field parameter. -/
theorem special_semilinear_torus_displacement
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (a : MulAut J.specialSubgroup) (σ : E ≃+* E) (u : J.unitarySubgroup)
    (h10 : u.val.val 1 0 = 0) (h20 : u.val.val 2 0 = 0)
    (h21 : u.val.val 2 1 = 0)
    (hu : ∀ x : J.specialSubgroup,
      (a x).val = u.val * GeneralLinearGroup.map σ.toRingHom x.val * u.val⁻¹)
    (k : Eˣ) :
    a (hermitianTorusSU J hJ k) *
        (hermitianTorusSU J hJ (Units.map σ.toMonoidHom k))⁻¹ ∈ specialRoot J hJ := by
  obtain ⟨z, hz⟩ := unitary_upper_torus_displacement J hJ u h10 h20 h21
    (Units.map σ.toMonoidHom k)
  refine ⟨z, Subtype.ext ?_⟩
  change hermitianUnipotentGL J z = (a (hermitianTorusSU J hJ k)).val *
    (hermitianTorusGL J (Units.map σ.toMonoidHom k))⁻¹
  rw [hu]
  change hermitianUnipotentGL J z =
    (u.val * GeneralLinearGroup.map σ.toRingHom (hermitianTorusGL J k) * u.val⁻¹) * _
  rw [field_map_torus]
  exact hz.symm

/-- The same field action holds on the full torus in the actual PSU carrier. -/
theorem projective_semilinear_torus_displacement
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (u : J.unitarySubgroup)
    (h10 : u.val.val 1 0 = 0) (h20 : u.val.val 2 0 = 0)
    (h21 : u.val.val 2 1 = 0)
    (hu : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk u.val * ProjGenLinGroup.map σ.toRingHom x.val *
        (ProjGenLinGroup.mk u.val)⁻¹) (k : Eˣ) :
    a (hermitianTorusPSU J hJ k) *
        (hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k))⁻¹ ∈ projectiveRoot J hJ := by
  obtain ⟨z, hz⟩ := unitary_upper_torus_displacement J hJ u h10 h20 h21
    (Units.map σ.toMonoidHom k)
  refine ⟨z, Subtype.ext ?_⟩
  change ProjGenLinGroup.mk (hermitianUnipotentGL J z) =
    (a (hermitianTorusPSU J hJ k)).val *
      (ProjGenLinGroup.mk (hermitianTorusGL J (Units.map σ.toMonoidHom k)))⁻¹
  rw [hu]
  change ProjGenLinGroup.mk (hermitianUnipotentGL J z) =
    (ProjGenLinGroup.mk u.val *
      ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.mk (hermitianTorusGL J k)) *
      (ProjGenLinGroup.mk u.val)⁻¹) * _
  rw [ProjGenLinGroup.map_mk, field_map_torus]
  simpa only [map_mul, map_inv] using congrArg ProjGenLinGroup.mk hz.symm

private theorem displacement_iff {G : Type*} [Group G] (U T : Subgroup G)
    (hdis : Disjoint U T) (x y z : G) (hy : y ∈ T) (hz : z ∈ T)
    (hxy : x * y⁻¹ ∈ U) : x * z⁻¹ ∈ U ↔ y = z := by
  have h : x * z⁻¹ ∈ U ↔ y * z⁻¹ ∈ U := by
    simpa only [mul_assoc, inv_mul_cancel_left] using
      (U.mul_mem_cancel_left (x := x * y⁻¹) (y := y * z⁻¹) hxy)
  rw [h]
  constructor
  · intro hm
    exact mul_inv_eq_one.mp (Subgroup.disjoint_def.mp hdis hm (T.mul_mem hy (T.inv_mem hz)))
  · rintro rfl
    simpa only [mul_inv_cancel] using U.one_mem

/-- Fixing a special torus element modulo the root is exactly fixing that
torus element under the field action. -/
theorem special_semilinear_torus_displacement_iff
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (a : MulAut J.specialSubgroup) (σ : E ≃+* E) (u : J.unitarySubgroup)
    (h10 : u.val.val 1 0 = 0) (h20 : u.val.val 2 0 = 0)
    (h21 : u.val.val 2 1 = 0)
    (hu : ∀ x : J.specialSubgroup,
      (a x).val = u.val * GeneralLinearGroup.map σ.toRingHom x.val * u.val⁻¹)
    (k : Eˣ) :
    a (hermitianTorusSU J hJ k) * (hermitianTorusSU J hJ k)⁻¹ ∈ specialRoot J hJ ↔
      hermitianTorusSU J hJ (Units.map σ.toMonoidHom k) = hermitianTorusSU J hJ k :=
  displacement_iff (specialRoot J hJ) (specialTorus J hJ)
    (special_root_disjoint_torus J hJ) _ _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
    (special_semilinear_torus_displacement J hJ a σ u h10 h20 h21 hu k)

/-- Fixing a projective torus element modulo the root is exactly equality in
the projective torus. This retains the cubic kernel of its parametrization. -/
theorem projective_semilinear_torus_displacement_iff
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (u : J.unitarySubgroup)
    (h10 : u.val.val 1 0 = 0) (h20 : u.val.val 2 0 = 0)
    (h21 : u.val.val 2 1 = 0)
    (hu : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk u.val * ProjGenLinGroup.map σ.toRingHom x.val *
        (ProjGenLinGroup.mk u.val)⁻¹) (k : Eˣ) :
    a (hermitianTorusPSU J hJ k) * (hermitianTorusPSU J hJ k)⁻¹ ∈ projectiveRoot J hJ ↔
      hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k) = hermitianTorusPSU J hJ k :=
  displacement_iff (projectiveRoot J hJ) (projectiveTorus J hJ)
    (projective_root_disjoint_torus J hJ) _ _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
    (projective_semilinear_torus_displacement J hJ a σ u h10 h20 h21 hu k)

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors
