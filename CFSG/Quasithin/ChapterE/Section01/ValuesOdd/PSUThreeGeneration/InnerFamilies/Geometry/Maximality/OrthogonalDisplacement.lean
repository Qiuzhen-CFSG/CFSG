module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Maximality.Coordinates
import Theory.LinearAlgebra.Hermitian.PrimeFrobeniusNormalization

/-!
# Orthogonal displacement in odd SU₃ block overgroups

Let `C` centralize `diag(-1,-1,1)` in the special unitary group of the identity
Hermitian form over a field of order `p²`. Every subgroup strictly containing
`C` contains a matrix whose last diagonal entry is zero. This supplies precisely
`OrthogonalDisplacement`, the first geometric premise in `Coordinates.lean`.

Write the third column of an element outside `C` as `(x,y,z)` and set
`s = conj(x)*x + conj(y)*y`. If `s` is nonzero, a determinant-one unitary block
normalizes the first two entries to `(d,0)`, where `conj(d)*d = s`. Norm
surjectivity then constructs a second block whose conjugate has last entry zero.

If the projection is isotropic, it is nonzero and `conj(z)*z = 1`. Choose a
nonfixed norm-one scalar `a` using the Cayley transform of a nonzero skew scalar.
Conjugating `diag(a,conj(a),1)` gives last entry `1+r`, where
`r = conj(x)*x*(a-conj(a))` is nonzero and skew. Its norm is `1-r²`, so the new
projection is nonisotropic and the first case applies. This argument includes
characteristic three and does not require transitivity on isotropic vectors.

Source: the unitary geometry used for Aschbacher--Smith, E.1.14(7), printed
p.214, A.2.3(2), p.33, and A.3.21(a), p.55; Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.Maximality
variable {F : Type*} [Field F]

private theorem adjoint_eq_inv (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) : J.conjTranspose g.val.val = (g⁻¹).val.val := by
  have h := ((J.mem_specialSubgroup_iff g.val).mp g.property).1
  rw [hJ, mul_one] at h
  exact (Units.mul_left_inj g.val).mp (h.trans (Units.inv_mul g.val).symm)

private theorem column_norm (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) :
    J.conj (g.val.val 0 2) * g.val.val 0 2 +
    J.conj (g.val.val 1 2) * g.val.val 1 2 +
    J.conj (g.val.val 2 2) * g.val.val 2 2 = 1 := by
  have h := ((J.mem_specialSubgroup_iff g.val).mp g.property).1
  rw [hJ, mul_one] at h
  simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
    add_assoc] using congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 2 2) h

private def planeRotation (J : HermitianForm 3 F) (hJ : J.form = 1)
    (a b : F) (hab : J.conj a * a + J.conj b * b = 1) : J.specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero
    !![a, -J.conj b, 0; b, J.conj a, 0; 0, 0, 1]
    (by simpa [Matrix.det_fin_three, mul_comm] using
      (show J.conj a * a + J.conj b * b ≠ 0 from hab ▸ one_ne_zero)), by
      rw [J.mem_specialSubgroup_iff, hJ]
      constructor
      · change J.conjTranspose !![a, -J.conj b, 0; b, J.conj a, 0; 0, 0, 1] * 1 *
          !![a, -J.conj b, 0; b, J.conj a, 0; 0, 0, 1] = 1
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
            J.conj_involutive a, J.conj_involutive b]
        all_goals first | (solve | ring) | (convert hab using 1 <;> ring)
      · apply Units.ext
        simpa [GeneralLinearGroup.val_det_apply, Matrix.det_fin_three, mul_comm] using hab⟩

private theorem planeRotation_mem (J : HermitianForm 3 F) (hJ : J.form = 1)
    (a b : F) (hab : J.conj a * a + J.conj b * b = 1) :
    planeRotation J hJ a b hab ∈
      centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) := by
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  change (!![a, -J.conj b, 0; b, J.conj a, 0; 0, 0, 1] *
    (SU3.standardInvolution J hJ).val.val) = _
  rw [SU3.standardInvolution_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeRotation, SU3.standardInvolution_val, Matrix.mul_apply, Fin.sum_univ_three]

private theorem conjugate_rotation_last (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) (a b : F) (hab : J.conj a * a + J.conj b * b = 1) :
    (g⁻¹ * planeRotation J hJ a b hab * g).val.val 2 2 =
    J.conj (g.val.val 0 2) * (a * g.val.val 0 2 - J.conj b * g.val.val 1 2) +
    J.conj (g.val.val 1 2) * (b * g.val.val 0 2 + J.conj a * g.val.val 1 2) +
    J.conj (g.val.val 2 2) * g.val.val 2 2 := by
  change (((g⁻¹).val.val * (planeRotation J hJ a b hab).val.val) * g.val.val) 2 2 = _
  rw [← adjoint_eq_inv J hJ g]
  simp [planeRotation, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem exists_norm [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hc : ∀ x, J.conj x = x ^ p)
    (hcard : Nat.card F = p ^ 2) (t : F) (ht : J.conj t = t) :
    ∃ b : F, J.conj b * b = t := by
  by_cases ht0 : t = 0
  · exact ⟨0, by simp [ht0]⟩
  obtain ⟨b, _, hb⟩ := J.exists_norm_of_prime_frobenius hc hcard t ht ht0
  exact ⟨b, by simpa only [mul_comm] using hb⟩

private theorem exists_norm_one_nonfixed [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (h2 : (2 : F) ≠ 0)
    (hc : ∀ x, J.conj x = x ^ p) (hcard : Nat.card F = p ^ 2) :
    ∃ a : F, J.conj a * a = 1 ∧ J.conj a ≠ a := by
  have hn : ∃ t : F, J.conj t ≠ t := by
    by_contra! h
    let e : {x : F // J.conj x = x} ≃ F :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, h x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he := Nat.card_congr e
    rw [J.card_fixed_of_prime_frobenius hc, hcard] at he
    have hp := (Fact.out : p.Prime).two_le
    nlinarith
  obtain ⟨t, ht⟩ := hn
  let r := t - J.conj t
  have hr : r ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hcr : J.conj r = -r := by
    simp only [r, map_sub, J.conj_involutive t]
    ring
  have hm : 1 - r ≠ 0 := by
    intro h
    have he : r = 1 := (sub_eq_zero.mp h).symm
    have hh := hcr
    rw [he, map_one] at hh
    exact h2 (by linear_combination hh)
  have hp : 1 + r ≠ 0 := by
    intro h
    have he : r = -1 := by linear_combination h
    have hh := hcr
    rw [he, map_neg, map_one] at hh
    exact h2 (by linear_combination -hh)
  refine ⟨(1 + r) / (1 - r), ?_, ?_⟩
  · simp only [map_div₀, map_add, map_sub, map_one, hcr, sub_neg_eq_add, ← sub_eq_add_neg]
    change (1 - r) / (1 + r) * ((1 + r) / (1 - r)) = 1
    field_simp
  · intro he
    simp only [map_div₀, map_add, map_sub, map_one, hcr, sub_neg_eq_add, ← sub_eq_add_neg] at he
    have he' : (1 - r) * (1 - r) = (1 + r) * (1 + r) :=
      (div_eq_div_iff hp hm).mp he
    have hz : (2 : F) * 2 * r = 0 := by linear_combination -he'
    exact hr ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero h2 h2))

private theorem normalize_projection (J : HermitianForm 3 F) (hJ : J.form = 1)
    (M : Subgroup J.specialSubgroup)
    (hM : centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) ≤ M)
    (g : J.specialSubgroup) (hg : g ∈ M) (d : F) (hd : d ≠ 0)
    (hn : J.conj d * d = J.conj (g.val.val 0 2) * g.val.val 0 2 +
      J.conj (g.val.val 1 2) * g.val.val 1 2) :
    ∃ k ∈ M, k.val.val 0 2 = d ∧ k.val.val 1 2 = 0 ∧ k.val.val 2 2 = g.val.val 2 2 := by
  let x := g.val.val 0 2
  let y := g.val.val 1 2
  have hcd : J.conj d ≠ 0 := (map_ne_zero J.conj).mpr hd
  have hab : J.conj (x / d) * (x / d) + J.conj (y / d) * (y / d) = 1 := by
    simp only [map_div₀, div_mul_div_comm, ← add_div]
    change (J.conj x * x + J.conj y * y) / (J.conj d * d) = 1
    rw [← hn, div_self (mul_ne_zero hcd hd)]
  let q := planeRotation J hJ (x / d) (y / d) hab
  refine ⟨q⁻¹ * g, M.mul_mem (M.inv_mem (hM (planeRotation_mem J hJ _ _ hab))) hg, ?_, ?_, ?_⟩
  · change ((q⁻¹).val.val * g.val.val) 0 2 = d
    rw [← adjoint_eq_inv J hJ q]
    simp [q, planeRotation, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_three, map_div₀]
    change J.conj x / J.conj d * x + J.conj y / J.conj d * y = d
    field_simp
    linear_combination -hn
  · change ((q⁻¹).val.val * g.val.val) 1 2 = 0
    rw [← adjoint_eq_inv J hJ q]
    simp [q, planeRotation, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_three, J.conj_involutive x, J.conj_involutive y, J.conj_involutive d]
    dsimp only [x, y]
    ring
  · change ((q⁻¹).val.val * g.val.val) 2 2 = g.val.val 2 2
    rw [← adjoint_eq_inv J hJ q]
    simp [q, planeRotation, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]

private theorem displacement_of_projection_nonisotropic [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (hc : ∀ x, J.conj x = x ^ p) (hcard : Nat.card F = p ^ 2)
    (M : Subgroup J.specialSubgroup)
    (hM : centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) ≤ M)
    (g : J.specialSubgroup) (hg : g ∈ M)
    (hs : J.conj (g.val.val 0 2) * g.val.val 0 2 +
      J.conj (g.val.val 1 2) * g.val.val 1 2 ≠ 0) :
    ∃ k ∈ M, k.val.val 2 2 = 0 := by
  let s := J.conj (g.val.val 0 2) * g.val.val 0 2 +
    J.conj (g.val.val 1 2) * g.val.val 1 2
  let t := J.conj (g.val.val 2 2) * g.val.val 2 2
  have hcs : J.conj s = s := by
    simp only [s, map_add, map_mul, J.conj_involutive (g.val.val 0 2),
      J.conj_involutive (g.val.val 1 2)]
    ring
  have hct : J.conj t = t := by
    simp only [t, map_mul, J.conj_involutive (g.val.val 2 2)]
    ring
  obtain ⟨d, hd⟩ := exists_norm p J hc hcard s hcs
  have hd0 : d ≠ 0 := by intro he; simp [he] at hd; exact hs hd.symm
  obtain ⟨k, hk, hk0, hk1, hk2⟩ := normalize_projection J hJ M hM g hg d hd0 hd
  let a := -t / s
  have hca : J.conj a = a := by simp only [a, map_div₀, map_neg, hct, hcs]
  obtain ⟨b, hb⟩ := exists_norm p J hc hcard (1 - a * a) (by
    simp only [map_sub, map_one, map_mul, hca])
  have hab : J.conj a * a + J.conj b * b = 1 := by rw [hca, hb]; ring
  refine ⟨k⁻¹ * planeRotation J hJ a b hab * k,
    M.mul_mem (M.mul_mem (M.inv_mem hk) (hM (planeRotation_mem J hJ a b hab))) hk, ?_⟩
  rw [conjugate_rotation_last, hk0, hk1, hk2]
  simp only [mul_zero, sub_zero, map_zero, zero_mul, add_zero]
  change J.conj d * (a * d) + t = 0
  calc
    _ = (J.conj d * d) * a + t := by ring
    _ = s * (-t / s) + t := by rw [hd]
    _ = 0 := by field_simp [show s ≠ 0 from hs]; ring

private theorem centralizer_of_projection_zero (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : J.specialSubgroup) (h02 : g.val.val 0 2 = 0) (h12 : g.val.val 1 2 = 0) :
    g ∈ centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) := by
  have hz : g.val.val 2 2 ≠ 0 := by
    intro he
    exact g.val.det_ne_zero (by simp [Matrix.det_fin_three, h02, h12, he])
  have hu := ((J.mem_specialSubgroup_iff g.val).mp g.property).1
  rw [hJ, mul_one] at hu
  have h20 : g.val.val 2 0 = 0 := by
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 2 0) hu
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, h02, h12] at he
    exact he.resolve_left hz
  have h21 : g.val.val 2 1 = 0 := by
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 2 1) hu
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, h02, h12] at he
    exact he.resolve_left hz
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  change g.val.val * (SU3.standardInvolution J hJ).val.val =
    (SU3.standardInvolution J hJ).val.val * g.val.val
  rw [SU3.standardInvolution_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21]

private theorem displacement_of_projection_isotropic [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hJ : J.form = 1) (h2 : (2 : F) ≠ 0)
    (hc : ∀ x, J.conj x = x ^ p) (hcard : Nat.card F = p ^ 2)
    (M : Subgroup J.specialSubgroup)
    (hM : centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) ≤ M)
    (g : J.specialSubgroup) (hg : g ∈ M)
    (hgC : g ∉ centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup))
    (hs : J.conj (g.val.val 0 2) * g.val.val 0 2 +
      J.conj (g.val.val 1 2) * g.val.val 1 2 = 0) :
    ∃ k ∈ M, k.val.val 2 2 = 0 := by
  let x := g.val.val 0 2
  let y := g.val.val 1 2
  let n := J.conj x * x
  have hx : x ≠ 0 := by
    intro he
    have hy : y = 0 := by
      change J.conj x * x + J.conj y * y = 0 at hs
      rw [he, map_zero, zero_mul, zero_add] at hs
      exact (mul_eq_zero.mp hs).elim (fun h => J.conj.injective (h.trans (map_zero J.conj).symm)) id
    exact hgC (centralizer_of_projection_zero J hJ g he hy)
  have hn : n ≠ 0 := mul_ne_zero ((map_ne_zero J.conj).mpr hx) hx
  have hcn : J.conj n = n := by
    simp only [n, map_mul, J.conj_involutive x]
    ring
  have hy : J.conj y * y = -n := by
    change n + J.conj y * y = 0 at hs
    linear_combination hs
  have ht : J.conj (g.val.val 2 2) * g.val.val 2 2 = 1 := by
    have he := column_norm J hJ g
    rw [hs, zero_add] at he
    exact he
  obtain ⟨a, ha, hca⟩ := exists_norm_one_nonfixed p J h2 hc hcard
  have hab : J.conj a * a + J.conj (0 : F) * 0 = 1 := by simpa using ha
  let k := g⁻¹ * planeRotation J hJ a 0 hab * g
  have hk : k ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem hg) (hM (planeRotation_mem J hJ a 0 hab))) hg
  let r := n * (a - J.conj a)
  have hr : r ≠ 0 := mul_ne_zero hn (sub_ne_zero.mpr (Ne.symm hca))
  have hcr : J.conj r = -r := by
    simp only [r, map_mul, map_sub, hcn, J.conj_involutive a]
    ring
  have hkr : k.val.val 2 2 = 1 + r := by
    rw [conjugate_rotation_last]
    simp only [map_zero, zero_mul, sub_zero, zero_add]
    change J.conj x * (a * x) + J.conj y * (J.conj a * y) + _ = _
    calc
      _ = n * a + (J.conj y * y) * J.conj a +
        J.conj (g.val.val 2 2) * g.val.val 2 2 := by dsimp [n]; ring
      _ = 1 + r := by rw [hy, ht]; dsimp [r]; ring
  apply displacement_of_projection_nonisotropic p J hJ hc hcard M hM k hk
  intro he
  have hh := column_norm J hJ k
  rw [he, zero_add, hkr, map_add, map_one, hcr] at hh
  have hz : r * r = 0 := by linear_combination -hh
  exact (mul_ne_zero hr hr) hz

/-- The full block centralizer over an odd prime quadratic field displaces
an orthogonal line inside every strictly larger subgroup. -/
theorem orthogonalDisplacement_of_prime_frobenius [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2)
    (hcard : Nat.card F = p ^ 2) (J : HermitianForm 3 F)
    (hJ : J.form = 1) (hc : ∀ x, J.conj x = x ^ p) :
    OrthogonalDisplacement J hJ := by
  intro M hM hne
  have hnle : ¬ M ≤ centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) :=
    fun h => hne (le_antisymm h hM)
  obtain ⟨g, hg, hgC⟩ := SetLike.not_le_iff_exists.mp hnle
  by_cases hs : J.conj (g.val.val 0 2) * g.val.val 0 2 +
      J.conj (g.val.val 1 2) * g.val.val 1 2 = 0
  · exact displacement_of_projection_isotropic p J hJ
      (CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp) hc hcard M hM g hg hgC hs
  · exact displacement_of_projection_nonisotropic p J hJ hc hcard M hM g hg hs

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.Maximality
