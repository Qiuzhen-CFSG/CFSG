module

public import Theory.SpecificGroups.SU3.OddRootFixers.NormalForms
public import Theory.SpecificGroups.SU3.EvenSemilinear.Coordinates
public import Mathlib.Algebra.CharP.Two

/-!
# Root conjugation of fourth powers of triangular unitary matrices

Over a field of characteristic two, an upper triangular unitary matrix with equal
outer diagonal entries has a fourth power conjugate to a diagonal matrix by a
special-unitary root element. If all diagonal entries agree, two squarings remove
the unipotent part. Otherwise the trace-surjective root coordinates let us remove
the first off-diagonal entry; unitarity removes the adjacent entry, and squaring
removes the remaining central entry. This statement imposes no order condition
on the original representative, so it also applies to scalar representatives.

Source: the diagonal-complement step of GLS4, Chapter 4, Lemma 3.6(c,d), with
Hermitian root coordinates from Huppert II.10.12. The actor-order and marked
Sylow transport are supplied by `TriangularConjugacy`.
-/

open Matrix BenderSuzuki.External
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private def rootUnitary (z : hermitianUnipotentCoord J) : J.unitarySubgroup :=
  ⟨(hermitianUnipotentSU J hJ z).val, (hermitianUnipotentSU J hJ z).property.1⟩

private theorem root_conj_entries (u : J.unitarySubgroup)
    (hu : IsRootTriangular J u) (z : hermitianUnipotentCoord J) :
    let v := rootUnitary J hJ z * u * (rootUnitary J hJ z)⁻¹
    IsRootTriangular J v ∧
      v.val.val 0 1 = u.val.val 0 1 + z.val.1 * (u.val.val 1 1 - u.val.val 0 0) := by
  have hi : (rootUnitary J hJ z)⁻¹ = rootUnitary J hJ z⁻¹ := by
    apply Subtype.ext
    exact congrArg (fun x : J.specialSubgroup => x.val) (map_inv (hermitianUnipotentSU J hJ) z).symm
  have hz1 : (z⁻¹).val.1 = -z.val.1 := rfl
  have hz2 : (z⁻¹).val.2 = J.conj z.val.2 := rfl
  dsimp only
  rw [hi]
  rcases hu with ⟨h10, h20, h21, hd⟩
  simp [IsRootTriangular, rootUnitary, hermitianUnipotentSU, hermitianUnipotentMatrix,
    hermitianUnipotentGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h10, h20, h21,
    hz1, hz2, hd]
  ring

include hJ in
private theorem triangular_zero01_zero12 (u : J.unitarySubgroup)
    (hu : IsRootTriangular J u) (h01 : u.val.val 0 1 = 0) : u.val.val 1 2 = 0 := by
  have he := (J.mem_unitarySubgroup_iff _).mp u.property
  rw [hJ] at he
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) he
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 2) he
  simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
    hu.2.2.1, h01] at h11 h12
  exact h12.resolve_left (right_ne_zero_of_mul_eq_one h11)

/-- Powers preserve diagonal shape and equality of the outer entries. -/
public theorem IsRootDiagonal.pow (d : J.unitarySubgroup) (hd : IsRootDiagonal J d) (k : ℕ) :
    IsRootDiagonal J (d ^ k) := by
  have hm : d.val.val = Matrix.diagonal (fun i => d.val.val i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply_ne _ hij, hd.1 i j hij]
  constructor
  · intro i j hij
    change (d.val.val ^ k) i j = 0
    rw [hm, Matrix.diagonal_pow]
    exact Matrix.diagonal_apply_ne _ hij
  · change (d.val.val ^ k) 0 0 = (d.val.val ^ k) 2 2
    rw [hm, Matrix.diagonal_pow]
    simp only [Matrix.diagonal_apply_eq, Pi.pow_apply, hd.2]

variable [CharP E 2]

omit [CharP E 2] in
private theorem triangular_square (u : J.unitarySubgroup) (hu : IsRootTriangular J u) :
    IsRootTriangular J (u ^ 2) := by
  rcases hu with ⟨h10, h20, h21, hd⟩
  change (u.val.val ^ 2) 1 0 = 0 ∧ (u.val.val ^ 2) 2 0 = 0 ∧
    (u.val.val ^ 2) 2 1 = 0 ∧ (u.val.val ^ 2) 0 0 = (u.val.val ^ 2) 2 2
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, hd]

include hJ in
private theorem diagonal_square (u : J.unitarySubgroup)
    (hu : IsRootTriangular J u) (h01 : u.val.val 0 1 = 0) :
    IsRootDiagonal J (u ^ 2) := by
  have h12 := triangular_zero01_zero12 J hJ u hu h01
  refine ⟨?_, (triangular_square J u hu).2.2.2⟩
  intro i j hij
  change (u.val.val ^ 2) i j = 0
  fin_cases i <;> fin_cases j <;>
    simp_all [pow_two, Matrix.mul_apply, Fin.sum_univ_three, hu.1, hu.2.1,
      hu.2.2.1, hu.2.2.2, mul_comm, CharTwo.add_self_eq_zero]

include hJ in
private theorem root_conjugate_fourth_diagonal [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (u : J.unitarySubgroup) (hu : IsRootTriangular J u) :
    ∃ z : hermitianUnipotentCoord J,
      IsRootDiagonal J ((rootUnitary J hJ z * u * (rootUnitary J hJ z)⁻¹) ^ 4) := by
  by_cases hm : u.val.val 0 0 = u.val.val 1 1
  · refine ⟨1, ?_⟩
    have hr : rootUnitary J hJ 1 = 1 := by
      apply Subtype.ext
      exact congrArg (fun x : J.specialSubgroup => x.val) (map_one (hermitianUnipotentSU J hJ))
    rw [hr, one_mul, inv_one, mul_one]
    have hz : (u ^ 2).val.val 0 1 = 0 := by
      change (u.val.val ^ 2) 0 1 = 0
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, hu.2.2.1, hm,
        mul_comm, CharTwo.add_self_eq_zero]
    simpa only [← pow_mul] using diagonal_square J hJ (u ^ 2) (triangular_square J u hu) hz
  · obtain ⟨z, hz⟩ := EvenSemilinear.coord_first_surjective J hcard hfixed
      (u.val.val 0 1 / (u.val.val 0 0 - u.val.val 1 1))
    change z.val.1 = u.val.val 0 1 / (u.val.val 0 0 - u.val.val 1 1) at hz
    obtain ⟨hv, h01⟩ := root_conj_entries J hJ u hu z
    have hzero : (rootUnitary J hJ z * u * (rootUnitary J hJ z)⁻¹).val.val 0 1 = 0 := by
      rw [h01, hz]
      field_simp [sub_ne_zero.mpr hm]
      ring
    refine ⟨z, ?_⟩
    simpa only [← pow_mul] using IsRootDiagonal.pow J _ (diagonal_square J hJ _ hv hzero) 2

/-- Every triangular root actor has a fourth power diagonalized by an element
of the actual special-unitary root group. No order condition on the representative
is required. -/
public theorem exists_root_conjugate_fourth_diagonal [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (u : J.unitarySubgroup) (hu : IsRootTriangular J u) :
    ∃ (r : J.specialSubgroup) (v : J.unitarySubgroup),
      r ∈ BorelTorus.specialRoot J hJ ∧
      v.val = r.val * u.val * r.val⁻¹ ∧ IsRootDiagonal J (v ^ 4) := by
  obtain ⟨z, hz⟩ := root_conjugate_fourth_diagonal J hJ hcard hfixed u hu
  exact ⟨hermitianUnipotentSU J hJ z,
    rootUnitary J hJ z * u * (rootUnitary J hJ z)⁻¹, ⟨z, rfl⟩, rfl, hz⟩

end BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
