module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.StandardRoots

/-!
# The standard unitary torus centralizer

Choose a norm-one parameter whose cube is not one. Its torus matrix has
one two-dimensional eigenspace and one one-dimensional eigenspace, so a
commuting special-unitary matrix has a corner block and a middle entry.
A norm-one square root removes the middle entry. The determinant and
unitarity equations then make every remaining entry fixed by the field
involution, placing the remainder in the actual root-generated SL₂.

For PSU₃, equality in the literal PGL quotient first gives a scalar.
The torus matrix has nonzero trace in characteristic two, and invariance
of trace under conjugation makes that scalar one. Projecting the special
factorization therefore proves the projective upper bound as well.

Source: GLS4, Chapter 4, Lemma 3.6(d). The trace argument follows the
calculation in Theory/SpecificGroups/SU3/UnitaryEight/MatrixCentralizer.lean,
here applied to the norm-one torus in every binary field size greater than two.
-/


open Matrix Subgroup BenderSuzuki.External
open BenderSuzuki.MatrixGroups HermitianForm HermitianForm.BorelTorus
open HermitianForm.BorelTorus.EvenCenterAction
open BenderSuzuki.ZD.RankOneModelGeometry
namespace BenderSuzuki.ZD.RankOneModelGeometry.UnitaryTorusCentralizer
variable {E : Type*} [Field E] [CharP E 2] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

omit [CharP E 2] in
private theorem torus_mem_fixed (k : Eˣ) (hk : J.conj (k : E) = (k : E)⁻¹) :
    hermitianTorusSU J hJ k ∈ specialTorus J hJ ⊓ centralizer ({hermitianWeylSU J hJ} : Set _) := by
  refine ⟨⟨k, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
  apply Subtype.ext
  apply Units.ext
  change hermitianTorusMatrix J k * hermitianWeylMatrix = hermitianWeylMatrix * hermitianTorusMatrix J k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, hermitianWeylMatrix, hk, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

private theorem projective_commutes_lifts (x : J.specialSubgroup) (k : Eˣ)
    (hk : J.conj (k : E) = (k : E)⁻¹)
    (hc : J.specialToProjective x * hermitianTorusPSU J hJ k =
      hermitianTorusPSU J hJ k * J.specialToProjective x) :
    x * hermitianTorusSU J hJ k = hermitianTorusSU J hJ k * x := by
  let A := x.val
  let B := hermitianTorusGL J k
  have htrace : B.val.trace ≠ 0 := by
    have ht : B.val.trace = (k : E)⁻¹ * (k : E)⁻¹ := by
      change (hermitianTorusMatrix J k).trace = _
      simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
      change (J.conj (k : E))⁻¹ + J.conj (k : E) * (k : E)⁻¹ + (k : E) = _
      rw [hk, inv_inv]
      linear_combination (k : E) * (CharTwo.two_eq_zero (R := E))
    rw [ht]
    exact mul_ne_zero (inv_ne_zero k.ne_zero) (inv_ne_zero k.ne_zero)
  have h : ProjGenLinGroup.mk A * ProjGenLinGroup.mk B =
      ProjGenLinGroup.mk B * ProjGenLinGroup.mk A := by
    simpa only [Subgroup.coe_mul, specialToProjective_apply_val, hermitianTorusPSU_val]
      using congrArg Subtype.val hc
  have hp : ProjGenLinGroup.mk (A * B * A⁻¹) = ProjGenLinGroup.mk B := by
    simpa only [map_mul, map_inv] using (mul_inv_eq_iff_eq_mul).mpr h
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have ht := congrArg (fun X : GL (Fin 3) E => X.val.trace) hc
  have hm : ((A * B * A⁻¹) * GeneralLinearGroup.scalar (Fin 3) c).val =
      (c : E) • (A.val * B.val * (A⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  rw [hm, trace_smul, trace_units_conj] at ht
  have hc1 : c = 1 := Units.ext (mul_right_cancel₀ htrace (ht.trans (one_mul _).symm))
  rw [hc1, map_one, mul_one] at hc
  exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hc)

omit [CharP E 2] in
private theorem block_shape_of_commutes (x : J.specialSubgroup) (k : Eˣ)
    (hk : J.conj (k : E) = (k : E)⁻¹) (hk3 : (k : E)^3 ≠ 1)
    (hc : x * hermitianTorusSU J hJ k = hermitianTorusSU J hJ k * x) :
    x.val.val 0 1 = 0 ∧ x.val.val 1 0 = 0 ∧ x.val.val 1 2 = 0 ∧ x.val.val 2 1 = 0 := by
  have hne : (k : E)⁻¹ * (k : E)⁻¹ ≠ (k : E) := by
    intro hh
    apply hk3
    have hh' := congrArg (fun z : E => z * (k : E)^2) hh
    field_simp at hh'
    linear_combination -hh'
  have entries (i j : Fin 3) := congrArg (fun z : J.specialSubgroup => z.val.val i j) hc
  have hh (i j : Fin 3) :
      (x.val.val * hermitianTorusMatrix J k) i j =
        (hermitianTorusMatrix J k * x.val.val) i j := entries i j
  have hz (v : E) (hv : v * ((k : E)⁻¹ * (k : E)⁻¹) = (k : E) * v) : v = 0 := by
    by_contra hv0
    exact hne (mul_left_cancel₀ hv0 (hv.trans (mul_comm _ _)))
  refine ⟨hz _ ?_, hz _ ?_, hz _ ?_, hz _ ?_⟩
  · simpa [hermitianTorusMatrix, hk, Matrix.mul_apply, Fin.sum_univ_three,
      div_eq_mul_inv, mul_assoc] using hh 0 1
  · simpa [hermitianTorusMatrix, hk, Matrix.mul_apply, Fin.sum_univ_three,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using (hh 1 0).symm
  · simpa [hermitianTorusMatrix, hk, Matrix.mul_apply, Fin.sum_univ_three,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using (hh 1 2).symm
  · simpa [hermitianTorusMatrix, hk, Matrix.mul_apply, Fin.sum_univ_three,
      div_eq_mul_inv, mul_assoc] using hh 2 1

private theorem fixed_of_block (x : J.specialSubgroup)
    (h01 : x.val.val 0 1 = 0) (h10 : x.val.val 1 0 = 0)
    (h12 : x.val.val 1 2 = 0) (h21 : x.val.val 2 1 = 0)
    (h11 : x.val.val 1 1 = 1) : x ∈ (specialGraphAut J hJ).fixedSubgroup := by
  let A := x.val.val
  obtain ⟨hp, hd⟩ := (J.mem_specialSubgroup_iff x.val).mp x.property
  have hd' := congrArg Units.val hd
  change A.det = 1 at hd'
  have hdet : A 0 0 * A 2 2 - A 0 2 * A 2 0 = 1 := by
    simpa [A, Matrix.det_fin_three, h01, h10, h12, h21, h11] using hd'
  have hh (i j : Fin 3) :
      J.conj (A 2 i) * A 0 j + J.conj (A 1 i) * A 1 j + J.conj (A 0 i) * A 2 j =
        (!![0,0,1;0,1,0;1,0,0] : Matrix (Fin 3) (Fin 3) E) i j := by
    simpa [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, A]
      using congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j) hp
  have h00 : J.conj (A 2 0) * A 0 0 + J.conj (A 0 0) * A 2 0 = 0 := by
    simpa [A, h10] using hh 0 0
  have h02 : J.conj (A 2 0) * A 0 2 + J.conj (A 0 0) * A 2 2 = 1 := by
    simpa [A, h10, h12] using hh 0 2
  have h20 : J.conj (A 2 2) * A 0 0 + J.conj (A 0 2) * A 2 0 = 1 := by
    simpa [A, h10, h12] using hh 2 0
  have h22 : J.conj (A 2 2) * A 0 2 + J.conj (A 0 2) * A 2 2 = 0 := by
    simpa [A, h12] using hh 2 2
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have ha : J.conj (A 0 0) = A 0 0 := by
    linear_combination A 0 0 * h02 - A 0 2 * h00 - J.conj (A 0 0) * hdet
  have hb : J.conj (A 0 2) = A 0 2 := by
    linear_combination A 0 0 * h22 - A 0 2 * h20 - J.conj (A 0 2) * hdet - A 0 2 * h2
  have hc : J.conj (A 2 0) = A 2 0 := by
    linear_combination A 2 2 * h00 - A 2 0 * h02 - J.conj (A 2 0) * hdet - A 2 0 * h2
  have hd : J.conj (A 2 2) = A 2 2 := by
    linear_combination A 2 2 * h20 - A 2 0 * h22 - J.conj (A 2 2) * hdet
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  apply Subtype.ext
  apply Units.ext
  rw [specialGraphAut_apply_val]
  ext i j
  change J.conj (A i j) = A i j
  fin_cases i <;> fin_cases j <;> simp [A, h01, h10, h12, h21, h11] at *
  all_goals assumption

private theorem factor_block [Finite E] (x : J.specialSubgroup)
    (h01 : x.val.val 0 1 = 0) (h10 : x.val.val 1 0 = 0)
    (h12 : x.val.val 1 2 = 0) (h21 : x.val.val 2 1 = 0) :
    x ∈ rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ) ⊔
      (specialTorus J hJ ⊓ centralizer ({hermitianWeylSU J hJ} : Set _)) := by
  let A := x.val.val
  have hp := ((J.mem_specialSubgroup_iff x.val).mp x.property).1
  have hn : J.conj (A 1 1) * A 1 1 = 1 := by
    simpa [A, hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
      h01, h21] using congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) hp
  have hm0 : A 1 1 ≠ 0 := by intro h; simp [h] at hn
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective (f := fun r : E => r^2)
    (fun a b : E => CharTwo.sq_inj.mp) ((A 1 1)⁻¹)
  change r^2 = (A 1 1)⁻¹ at hr
  have hr0 : r ≠ 0 := by
    intro h
    have he : (A 1 1)⁻¹ = 0 := by simpa [h] using hr.symm
    exact inv_ne_zero hm0 he
  let k : Eˣ := Units.mk0 r hr0
  have hk : J.conj (k : E) = (k : E)⁻¹ := by
    change J.conj r = r⁻¹
    apply CharTwo.sq_inj.mp
    rw [← map_pow, hr, map_inv₀, inv_pow, hr, inv_inv,
      eq_inv_of_mul_eq_one_left hn, inv_inv]

  let y := x * (hermitianTorusSU J hJ k)⁻¹
  have hy (i j : Fin 3) : y.val.val i j =
      (A * hermitianTorusMatrix J k⁻¹) i j := by
    change (x * (hermitianTorusSU J hJ k)⁻¹).val.val i j = _
    rw [← map_inv]
    rfl
  have hy01 : y.val.val 0 1 = 0 := by
    rw [hy]; simp [hermitianTorusMatrix, Matrix.mul_apply, Fin.sum_univ_three, A, h01]
  have hy10 : y.val.val 1 0 = 0 := by
    rw [hy]; simp [hermitianTorusMatrix, Matrix.mul_apply, Fin.sum_univ_three, A, h10]
  have hy12 : y.val.val 1 2 = 0 := by
    rw [hy]; simp [hermitianTorusMatrix, Matrix.mul_apply, Fin.sum_univ_three, A, h12]
  have hy21 : y.val.val 2 1 = 0 := by
    rw [hy]; simp [hermitianTorusMatrix, Matrix.mul_apply, Fin.sum_univ_three, A, h21]
  have hy11 : y.val.val 1 1 = 1 := by
    rw [hy]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    change A 1 0 * 0 + A 1 1 * (J.conj ((k⁻¹ : Eˣ) : E) * (((k⁻¹ : Eˣ) : E))⁻¹) + A 1 2 * 0 = 1
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hk, inv_inv,
      mul_zero, zero_add, add_zero]
    change A 1 1 * (r * r) = 1
    rw [← pow_two, hr, mul_inv_cancel₀ hm0]
  have hyR : y ∈ rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ) := by
    rw [UnitaryStandardRoots.special_generated_eq_fixed]
    exact fixed_of_block J hJ y hy01 hy10 hy12 hy21 hy11
  have hx : x = y * hermitianTorusSU J hJ k := by simp [y]
  rw [hx]
  exact mul_mem (mem_sup_left hyR) (mem_sup_right (torus_mem_fixed J hJ k hk))

omit [CharP E 2] in
private theorem projection_fixed_le :
    (specialTorus J hJ ⊓ centralizer ({hermitianWeylSU J hJ} : Set _)).map J.specialToProjective ≤
      projectiveTorus J hJ ⊓ centralizer ({hermitianWeylPSU J hJ} : Set _) := by
  rintro _ ⟨x, hx, rfl⟩
  constructor
  · rw [← UnitaryStandardRoots.projection_torus]
    exact mem_map_of_mem _ hx.1
  · apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg J.specialToProjective (mem_centralizer_singleton_iff.mp hx.2)
    simpa only [map_mul, UnitaryStandardRoots.projection_weyl] using hh

omit [CharP E 2] in
private theorem projection_torus_apply (k : Eˣ) :
    J.specialToProjective (hermitianTorusSU J hJ k) = hermitianTorusPSU J hJ k := by
  apply Subtype.ext
  rw [specialToProjective_apply_val, hermitianTorusPSU_val]
  rfl

variable [Finite E] {q : ℕ}

/-- The fixed standard torus centralizer in SU₃ lies in the root–torus join. -/
public theorem special_standard_le (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {z : E // J.conj z = z} = q) (hq : 2 < q) :
    centralizer (specialTorus J hJ ⊓ centralizer ({hermitianWeylSU J hJ} : Set _) : Set _) ≤
      rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ) ⊔
        (specialTorus J hJ ⊓ centralizer ({hermitianWeylSU J hJ} : Set _)) := by
  obtain ⟨k, _, hk3, _, hk⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one J q hcard hfixed hJ hq
  intro x hx
  have hc := (hx _ (torus_mem_fixed J hJ k hk)).symm
  obtain ⟨h01, h10, h12, h21⟩ := block_shape_of_commutes J hJ x k hk hk3 hc
  exact factor_block J hJ x h01 h10 h12 h21

/-- The same upper bound in the actual projective special-unitary image. -/
public theorem projective_standard_le (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {z : E // J.conj z = z} = q) (hq : 2 < q) :
    centralizer (projectiveTorus J hJ ⊓ centralizer ({hermitianWeylPSU J hJ} : Set _) : Set _) ≤
      rootGenerated (projectiveRoot J hJ) (hermitianWeylPSU J hJ) ⊔
        (projectiveTorus J hJ ⊓ centralizer ({hermitianWeylPSU J hJ} : Set _)) := by
  obtain ⟨k, _, hk3, _, hk⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one J q hcard hfixed hJ hq
  intro x hx
  obtain ⟨y, rfl⟩ := J.specialToProjective_surjective x
  have ht := projection_fixed_le J hJ
    (mem_map_of_mem J.specialToProjective (torus_mem_fixed J hJ k hk))
  rw [projection_torus_apply] at ht
  have hc := projective_commutes_lifts J hJ y k hk (hx _ ht).symm
  obtain ⟨h01, h10, h12, h21⟩ := block_shape_of_commutes J hJ y k hk hk3 hc
  have hy := factor_block J hJ y h01 h10 h12 h21
  have hm := mem_map_of_mem J.specialToProjective hy
  rw [Subgroup.map_sup, UnitaryStandardRoots.projection_rootGenerated] at hm
  exact (sup_le_sup_left (projection_fixed_le J hJ) _) hm

end BenderSuzuki.ZD.RankOneModelGeometry.UnitaryTorusCentralizer
