module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Maximality.Coordinates
public import Theory.LinearAlgebra.Hermitian.PrimeFrobeniusNormalization

/-!
# Generation by two orthogonal line stabilizers in SU₃

For the identity Hermitian form over a field of order `p²`, with odd `p` and
prime Frobenius conjugation, the full centralizers of `diag(-1,-1,1)` and its
conjugate by an orthogonal displacement generate the actual special unitary
group. This proves the `OrthogonalGeneration` input to
`standard_centralizer_isCoatom_of_orthogonal_geometry`.

A two-coordinate unitary rotation factors each orthogonal displacement as
`u * coordinateCycle * v`, with both `u` and `v` in the original centralizer.
For the coordinate pair, two signed swaps produce the coordinate cycle. Given
any special unitary matrix, its last column has norm one. In odd characteristic
some pair of its coordinates has nonzero combined norm. Norm surjectivity
normalizes that pair, and a determinant-one unitary rotation zeros one entry.
A cyclic permutation then reduces to the orthogonal factorization. This proves
generation directly, also for `p = 3`.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(7), printed p.214, and the unitary centralizer in A.3.21(a), printed p.55;
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.11.
The matrix-generation argument here supplies the geometric prerequisite;
unconditional maximality still needs the independent orthogonal-displacement input.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.Maximality
variable {F : Type*} [Field F]

private abbrev C (J : HermitianForm 3 F) (hJ : J.form = 1) :=
  centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup)

private theorem unitary_eq (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) : J.conjTranspose g.val.val * g.val.val = 1 := by
  simpa only [hJ, mul_one] using ((J.mem_specialSubgroup_iff _).mp g.property).1

private theorem inverse_eq (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) : g⁻¹.val.val = J.conjTranspose g.val.val := by
  apply (Units.mul_left_inj g.val).mp
  exact (congrArg Units.val (inv_mul_cancel g.val)).trans (unitary_eq J hJ g).symm

private theorem column_norm (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) :
    J.conj (g.val.val 0 2) * g.val.val 0 2 +
      J.conj (g.val.val 1 2) * g.val.val 1 2 +
      J.conj (g.val.val 2 2) * g.val.val 2 2 = 1 := by
  simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three] using
    congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 2 2) (unitary_eq J hJ g)

private theorem mem_C_of_column (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) (h0 : g.val.val 0 2 = 0) (h1 : g.val.val 1 2 = 0) :
    g ∈ C J hJ := by
  have hn := column_norm J hJ g
  rw [h0, h1] at hn
  simp only [map_zero, mul_zero, zero_add] at hn
  have hn0 : J.conj (g.val.val 2 2) ≠ 0 := left_ne_zero_of_mul_eq_one hn
  have he (i : Fin 3) := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 2 i)
    (unitary_eq J hJ g)
  have h20 := he 0
  have h21 := he 1
  simp only [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, h0, h1,
    map_zero, zero_mul, zero_add, Matrix.one_apply, Fin.reduceEq, if_false] at h20 h21
  have h20' : g.val.val 2 0 = 0 := (mul_eq_zero.mp h20).resolve_left hn0
  have h21' : g.val.val 2 1 = 0 := (mul_eq_zero.mp h21).resolve_left hn0
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  apply Units.ext
  change g.val.val * (SU3.standardInvolution J hJ).val.val =
    (SU3.standardInvolution J hJ).val.val * g.val.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SU3.standardInvolution_val, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h20', h21']

/-- A determinant-one unitary rotation in the first two coordinates. -/
private noncomputable def rotation (J : HermitianForm 3 F) (hJ : J.form = 1)
    (a b : F) (hab : J.conj a * a + J.conj b * b = 1) : J.specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![a, -J.conj b, 0; b, J.conj a, 0; 0, 0, 1]
    (by
      have hd : (!![a, -J.conj b, 0; b, J.conj a, 0; 0, 0, 1]).det = 1 := by
        simpa [Matrix.det_fin_three, mul_comm] using hab
      rw [hd]
      exact one_ne_zero), by
      rw [J.mem_specialSubgroup_iff, hJ]
      constructor
      · change J.conjTranspose !![a, -J.conj b, 0; b, J.conj a, 0; 0, 0, 1] * 1 *
          !![a, -J.conj b, 0; b, J.conj a, 0; 0, 0, 1] = 1
        rw [mul_one]
        have hcc (x : F) : J.conj (J.conj x) = x := J.conj_involutive x
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hcc]
        · exact hab
        · ring
        · ring
        · linear_combination hab
      · apply Units.ext
        simpa [GeneralLinearGroup.val_det_apply, Matrix.det_fin_three, mul_comm] using hab⟩

private theorem rotation_val (J : HermitianForm 3 F) (hJ : J.form = 1)
    (a b : F) (hab : J.conj a * a + J.conj b * b = 1) :
    (rotation J hJ a b hab).val.val =
      !![a, -J.conj b, 0; b, J.conj a, 0; 0, 0, 1] := rfl

private theorem rotation_mem (J : HermitianForm 3 F) (hJ : J.form = 1)
    (a b : F) (hab : J.conj a * a + J.conj b * b = 1) :
    rotation J hJ a b hab ∈ C J hJ := mem_C_of_column J hJ _ rfl rfl

private theorem cycle_val (J : HermitianForm 3 F) (hJ : J.form = 1) :
    (coordinateCycle J hJ).val.val = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

/-- An orthogonal displacement lies in the double coset of the coordinate cycle. -/
private theorem orthogonal_factorization (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) (hg : g.val.val 2 2 = 0) :
    ∃ u ∈ C J hJ, ∃ v ∈ C J hJ, g = u * coordinateCycle J hJ * v := by
  have hab : J.conj (g.val.val 0 2) * g.val.val 0 2 +
      J.conj (g.val.val 1 2) * g.val.val 1 2 = 1 := by
    simpa only [hg, map_zero, mul_zero, add_zero] using column_norm J hJ g
  let u := rotation J hJ (g.val.val 0 2) (g.val.val 1 2) hab
  let v := (coordinateCycle J hJ)⁻¹ * (u⁻¹ * g)
  refine ⟨u, rotation_mem J hJ _ _ hab, v, ?_, ?_⟩
  · apply mem_C_of_column J hJ
    · change ((coordinateCycle J hJ)⁻¹.val.val * (u⁻¹.val.val * g.val.val)) 0 2 = 0
      rw [inverse_eq J hJ, inverse_eq J hJ]
      simp [u, rotation_val, cycle_val, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_three]
      rw [J.conj_involutive, J.conj_involutive]
      ring
    · change ((coordinateCycle J hJ)⁻¹.val.val * (u⁻¹.val.val * g.val.val)) 1 2 = 0
      rw [inverse_eq J hJ, inverse_eq J hJ]
      simp [u, rotation_val, cycle_val, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_three, hg]
  · dsimp [v]
    group

private theorem orthogonal_mem (J : HermitianForm 3 F) (hJ : J.form = 1)
    (M : Subgroup J.specialSubgroup) (hC : C J hJ ≤ M)
    (hq : coordinateCycle J hJ ∈ M)
    (g : J.specialSubgroup) (hg : g.val.val 2 2 = 0) : g ∈ M := by
  obtain ⟨u, hu, v, hv, rfl⟩ := orthogonal_factorization J hJ g hg
  exact M.mul_mem (M.mul_mem (hC hu) hq) (hC hv)

/-- Two signed coordinate swaps multiply to the coordinate cycle. -/
private theorem cycle_mem_join (J : HermitianForm 3 F) (hJ : J.form = 1) :
    coordinateCycle J hJ ∈ C J hJ ⊔
      (C J hJ).map (MulAut.conj (coordinateCycle J hJ)).toMonoidHom := by
  let r := rotation J hJ 0 1 (by simp)
  have hr : r ∈ C J hJ := rotation_mem J hJ _ _ _
  have he : coordinateCycle J hJ = r * ((MulAut.conj (coordinateCycle J hJ)) r) := by
    apply Subtype.ext
    apply Units.ext
    change (coordinateCycle J hJ).val.val = r.val.val *
      ((coordinateCycle J hJ).val.val * r.val.val * (coordinateCycle J hJ)⁻¹.val.val)
    rw [inverse_eq J hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [r, rotation_val, cycle_val, HermitianForm.conjTranspose, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_three]
  have hm : r * ((MulAut.conj (coordinateCycle J hJ)) r) ∈ C J hJ ⊔
      (C J hJ).map (MulAut.conj (coordinateCycle J hJ)).toMonoidHom :=
    mul_mem (mem_sup_left hr) (mem_sup_right (mem_map.mpr ⟨r, hr, rfl⟩))
  simpa only [← he] using hm

private theorem generation_of_coordinate_pair (J : HermitianForm 3 F) (hJ : J.form = 1)
    (hgen : C J hJ ⊔ (C J hJ).map
      (MulAut.conj (coordinateCycle J hJ)).toMonoidHom = ⊤) :
    OrthogonalGeneration J hJ := by
  intro g hg
  obtain ⟨u, hu, v, hv, hguv⟩ := orthogonal_factorization J hJ g hg
  let M := C J hJ ⊔ (C J hJ).map (MulAut.conj g).toMonoidHom
  change M = ⊤
  apply top_unique
  rw [← hgen]
  refine sup_le le_sup_left ?_
  rintro _ ⟨c, hc, rfl⟩
  have hvch : v⁻¹ * c * v ∈ C J hJ :=
    mul_mem (mul_mem (inv_mem hv) hc) hv
  have hgc : g * (v⁻¹ * c * v) * g⁻¹ ∈ M :=
    mem_sup_right (mem_map.mpr ⟨v⁻¹ * c * v, hvch, rfl⟩)
  have huM : u ∈ M := mem_sup_left hu
  have he : (MulAut.conj (coordinateCycle J hJ)) c =
      u⁻¹ * (g * (v⁻¹ * c * v) * g⁻¹) * u := by
    rw [MulAut.conj_apply, hguv]
    group
  change (MulAut.conj (coordinateCycle J hJ)) c ∈ M
  rw [he]
  exact M.mul_mem (M.mul_mem (M.inv_mem huM) hgc) huM

/-- A nonzero pair norm permits a unitary rotation that zeros one entry. -/
private theorem mem_of_pair_norm_ne_zero [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Nat.card F = p ^ 2) (J : HermitianForm 3 F) (hJ : J.form = 1)
    (hc : ∀ x, J.conj x = x ^ p)
    (M : Subgroup J.specialSubgroup) (hC : C J hJ ≤ M)
    (hq : coordinateCycle J hJ ∈ M) (g : J.specialSubgroup)
    (hs : J.conj (g.val.val 0 2) * g.val.val 0 2 +
      J.conj (g.val.val 1 2) * g.val.val 1 2 ≠ 0) : g ∈ M := by
  let a := g.val.val 0 2
  let b := g.val.val 1 2
  have hfix : J.conj (J.conj a * a + J.conj b * b) =
      J.conj a * a + J.conj b * b := by
    rw [map_add, map_mul, map_mul, J.conj_involutive, J.conj_involutive]
    ring
  obtain ⟨t, _, ht⟩ := J.exists_norm_of_prime_frobenius hc hcard _ hfix hs
  have hab : J.conj (a / t) * (a / t) + J.conj (b / t) * (b / t) = 1 := by
    rw [map_div₀, map_div₀, div_mul_div_comm, div_mul_div_comm, ← add_div,
      mul_comm (J.conj t) t, ht]
    exact div_self hs
  let r := rotation J hJ (a / t) (b / t) hab
  have hr : r ∈ M := hC (rotation_mem J hJ _ _ hab)
  have hcc (x : F) : J.conj (J.conj x) = x := J.conj_involutive x
  have hy : coordinateCycle J hJ * (r⁻¹ * g) ∈ M := by
    apply orthogonal_mem J hJ M hC hq
    change ((coordinateCycle J hJ).val.val * (r⁻¹.val.val * g.val.val)) 2 2 = 0
    rw [inverse_eq J hJ]
    simp [r, rotation_val, cycle_val, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_three, hcc]
    dsimp [a, b]
    ring
  have hm := M.mul_mem hr (M.mul_mem (M.inv_mem hq) hy)
  simpa only [inv_mul_cancel_left, mul_inv_cancel_left] using hm

private theorem cycle_mul_rows (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) (j : Fin 3) :
    (coordinateCycle J hJ * g).val.val 0 j = g.val.val 2 j ∧
    (coordinateCycle J hJ * g).val.val 1 j = g.val.val 0 j ∧
    (coordinateCycle J hJ * g).val.val 2 j = g.val.val 1 j := by
  change ((coordinateCycle J hJ).val.val * g.val.val) 0 j = _ ∧
    ((coordinateCycle J hJ).val.val * g.val.val) 1 j = _ ∧
    ((coordinateCycle J hJ).val.val * g.val.val) 2 j = _
  simp [cycle_val, Matrix.mul_apply, Fin.sum_univ_three]

/-- Odd characteristic guarantees a nonzero pair norm after a cyclic permutation. -/
private theorem eq_top_of_cycle_mem [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hc : ∀ x, J.conj x = x ^ p)
    (M : Subgroup J.specialSubgroup) (hC : C J hJ ≤ M)
    (hq : coordinateCycle J hJ ∈ M) : M = ⊤ := by
  have h2 : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp
  apply (Subgroup.eq_top_iff' M).mpr
  intro g
  by_cases hab : J.conj (g.val.val 0 2) * g.val.val 0 2 +
      J.conj (g.val.val 1 2) * g.val.val 1 2 = 0
  · by_cases hca : J.conj (g.val.val 2 2) * g.val.val 2 2 +
        J.conj (g.val.val 0 2) * g.val.val 0 2 = 0
    · have hbc : J.conj (g.val.val 1 2) * g.val.val 1 2 +
          J.conj (g.val.val 2 2) * g.val.val 2 2 ≠ 0 := by
        intro hh
        have hn := column_norm J hJ g
        apply h2
        linear_combination hab + hca + hh - 2 * hn
      have hm : coordinateCycle J hJ * (coordinateCycle J hJ * g) ∈ M := by
        apply mem_of_pair_norm_ne_zero hcard J hJ hc M hC hq
        rw [(cycle_mul_rows J hJ _ 2).1, (cycle_mul_rows J hJ _ 2).2.1,
          (cycle_mul_rows J hJ _ 2).2.2, (cycle_mul_rows J hJ _ 2).1]
        exact hbc
      have hm' := M.mul_mem (M.inv_mem hq) (M.mul_mem (M.inv_mem hq) hm)
      simpa only [inv_mul_cancel_left] using hm'
    · have hm : coordinateCycle J hJ * g ∈ M := by
        apply mem_of_pair_norm_ne_zero hcard J hJ hc M hC hq
        rw [(cycle_mul_rows J hJ _ 2).1, (cycle_mul_rows J hJ _ 2).2.1]
        exact hca
      simpa only [inv_mul_cancel_left] using M.mul_mem (M.inv_mem hq) hm
  · exact mem_of_pair_norm_ne_zero hcard J hJ hc M hC hq g hab

/-- The full stabilizers of two orthogonal nonisotropic lines generate the actual
special unitary group over every field of order `p²` for an odd prime `p`,
including characteristic three. The conjugation is `c ↦ g * c * g⁻¹`. -/
theorem orthogonalGeneration [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hc : ∀ x, J.conj x = x ^ p) :
    OrthogonalGeneration J hJ :=
  generation_of_coordinate_pair J hJ
    (eq_top_of_cycle_mem hp hcard J hJ hc _ le_sup_left (cycle_mem_join J hJ))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.Maximality
