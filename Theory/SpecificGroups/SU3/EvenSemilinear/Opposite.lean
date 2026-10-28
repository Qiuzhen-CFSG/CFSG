module

public import Theory.SpecificGroups.SU3.EvenSemilinear.Rigidity
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.FirstField

/-!
# Compatible opposite-root formulas in characteristic two

The upper first-coordinate formula and torus preservation give the full
upper formula by binary coordinate rigidity. A Bruhat relation then fixes
the Weyl-image parameter. Comparing two entries of the opposite matrix,
while retaining the projective scalar, gives both opposite coordinates.
Thus one genuine unitary diagonal matrix realizes both root formulas.

The torus, Weyl-coset and first-coordinate normalizations are explicit
hypotheses here, discharged by the final coverage assembly.
Source: Steinberg, Theorem 36, steps (4)–(7),
`refs/KGroup/GLS3/Chapter2St1.tex`; matrix conventions: Huppert II.10.12.
-/

public section
open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private theorem weylGL_inv : (hermitianWeylGL : GL (Fin 3) E)⁻¹ = hermitianWeylGL := by
  apply inv_eq_of_mul_eq_one_left
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem weyl_inv : (weyl J hJ)⁻¹ = weyl J hJ := by
  apply Subtype.ext
  simp only [Subgroup.coe_inv, hermitianWeylPSU_val, ← map_inv, weylGL_inv]

-- The bottom row of the left matrix is `(k² b, -conj(k) a, k/conj(k))`.
-- The right bottom row is `l * (1, r.1, r.2)`, so their ratio removes the scalar.
private theorem bruhat_image_ratio (k l : Eˣ) (x y r : hermitianUnipotentCoord J)
    (h : (hermitianTorusPSU J hJ k * weyl J hJ) * root J hJ x *
        (hermitianTorusPSU J hJ k * weyl J hJ) =
      root J hJ y * hermitianTorusPSU J hJ l * weyl J hJ * root J hJ r) :
    J.conj (k : E) * x.val.1 + (k : E) ^ 2 * x.val.2 * r.val.1 = 0 := by
  have hp := congrArg Subtype.val h
  simp only [Subgroup.coe_mul, hermitianTorusPSU_val, hermitianWeylPSU_val,
    hermitianUnipotentPSU_val, ← map_mul] at hp
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h20 := congrArg (fun M : GL (Fin 3) E => M.val 2 0) hc
  have h21 := congrArg (fun M : GL (Fin 3) E => M.val 2 1) hc
  simp [GeneralLinearGroup.coe_scalar,
    hermitianUnipotentGL, hermitianUnipotentMatrix, hermitianTorusGL,
    hermitianTorusMatrix, hermitianWeylGL, hermitianWeylMatrix,
    Matrix.mul_apply, Fin.sum_univ_three] at h20 h21
  field_simp at h21
  apply mul_left_cancel₀ (Units.ne_zero c)
  linear_combination -h21 + r.val.1 * h20

-- The middle diagonal entry fixes the projective scalar for the comparison
-- with an opposite root. Its bottom middle entry then recovers the first coordinate.
private theorem opposite_image_first (k : Eˣ) (x v : hermitianUnipotentCoord J)
    (h : oppositeRoot J hJ v =
      (hermitianTorusPSU J hJ k * weyl J hJ) * root J hJ x *
        (hermitianTorusPSU J hJ k * weyl J hJ)) :
    J.conj (k : E) * v.val.1 = (k : E) ^ 2 * x.val.1 := by
  have hp := congrArg Subtype.val h
  simp only [oppositeRoot_apply, weyl_inv, Subgroup.coe_mul,
    hermitianTorusPSU_val, hermitianWeylPSU_val, hermitianUnipotentPSU_val,
    ← map_mul] at hp
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h11 := congrArg (fun M : GL (Fin 3) E => M.val 1 1) hc
  have h21 := congrArg (fun M : GL (Fin 3) E => M.val 2 1) hc
  simp [GeneralLinearGroup.coe_scalar,
    hermitianUnipotentGL, hermitianUnipotentMatrix, hermitianTorusGL,
    hermitianTorusMatrix, hermitianWeylGL, hermitianWeylMatrix,
    Matrix.mul_apply, Fin.sum_univ_three] at h11 h21
  rw [h11] at h21
  field_simp at h21
  simpa only [mul_comm] using h21

private theorem opposite_image_second (k : Eˣ) (x v : hermitianUnipotentCoord J)
    (h : oppositeRoot J hJ v =
      (hermitianTorusPSU J hJ k * weyl J hJ) * root J hJ x *
        (hermitianTorusPSU J hJ k * weyl J hJ)) :
    J.conj (k : E) ^ 2 * v.val.2 = (k : E) ^ 4 * x.val.2 := by
  have hp := congrArg Subtype.val h
  simp only [oppositeRoot_apply, weyl_inv, Subgroup.coe_mul,
    hermitianTorusPSU_val, hermitianWeylPSU_val, hermitianUnipotentPSU_val,
    ← map_mul] at hp
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h11 := congrArg (fun M : GL (Fin 3) E => M.val 1 1) hc
  have h20 := congrArg (fun M : GL (Fin 3) E => M.val 2 0) hc
  simp [GeneralLinearGroup.coe_scalar,
    hermitianUnipotentGL, hermitianUnipotentMatrix, hermitianTorusGL,
    hermitianTorusMatrix, hermitianWeylGL, hermitianWeylMatrix,
    Matrix.mul_apply, Fin.sum_univ_three] at h11 h20
  rw [h11] at h20
  field_simp at h20
  linear_combination h20

/-- Upper semilinearity forces the matching full opposite coordinate formula.
The torus and Weyl-coset hypotheses are explicit normalization inputs. -/
theorem oppositeCoordinateAut_eq_scaled_of_root_first [Finite E] [CharP E 2]
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) (hq : 2 < q)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hV : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ)
    (hT : (rootTorus J hJ).map b.toMonoidHom = rootTorus J hJ)
    (hw : ∃ k : Eˣ, b (weyl J hJ) = hermitianTorusPSU J hJ k * weyl J hJ)
    (σ : E ≃+* E) (t : Eˣ)
    (hfirst : ∀ z : hermitianUnipotentCoord J,
      (rootCoordinateAut J hJ b hU z).val.1 = (t : E) * σ z.val.1) :
    oppositeCoordinateAut J hJ b hV =
      scaledFieldCoordAut J σ (Units.map J.conj.toMonoidHom t)⁻¹ := by
  have hcoord := coordAut_eq_scaledField_of_first J hcard hfixed hJ hq
    (rootCoordinateAut J hJ b hU) σ t hfirst
    (rootCoordinateAut_torus_intertwining J hJ b hU hT)
  have hu (z : hermitianUnipotentCoord J) :
      b (root J hJ z) = root J hJ (scaledFieldCoordAut J σ t z) := by
    rw [← rootCoordinateAut_spec J hJ b hU z, hcoord]
  obtain ⟨k, hk⟩ := hw
  obtain ⟨z, hz⟩ := coord_first_surjective J hcard hfixed 1
  change z.val.1 = 1 at hz
  have hz2 : z.val.2 ≠ 0 := by
    intro h
    have he := z.property
    simp [h, hz] at he
  have htorus : b (hermitianTorusPSU J hJ (Units.mk0 z.val.2 hz2)) ∈ rootTorus J hJ := by
    rw [← hT]
    exact ⟨hermitianTorusPSU J hJ (Units.mk0 z.val.2 hz2), ⟨_, rfl⟩, rfl⟩
  obtain ⟨l, hl⟩ := htorus
  have he := congrArg b (hermitianWeylPSU_mul_unipotent_mul_weyl J hJ z hz2)
  simp only [map_mul, hu, hk, ← hl] at he
  have hratio := bruhat_image_ratio J hJ k (l * k)
    (scaledFieldCoordAut J σ t z)
    (scaledFieldCoordAut J σ t (hermitianBruhatLeft J z hz2))
    (scaledFieldCoordAut J σ t (hermitianBruhatRight J z hz2)) (by
      simpa only [map_mul, mul_assoc] using he)
  simp only [scaledFieldCoordAut_fst, scaledFieldCoordAut_snd,
    hermitianBruhatRight, map_div₀, map_neg, hz, map_one] at hratio
  have hs : σ z.val.2 ≠ 0 := (map_ne_zero σ).mpr hz2
  have hscale : J.conj (k : E) = (k : E) ^ 2 * ((t : E) * J.conj (t : E)) := by
    field_simp [hs] at hratio
    apply mul_left_cancel₀ (Units.ne_zero t)
    linear_combination hratio
  apply MulEquiv.ext
  intro v
  have himage : oppositeRoot J hJ (oppositeCoordinateAut J hJ b hV v) =
      (hermitianTorusPSU J hJ k * weyl J hJ) * root J hJ (scaledFieldCoordAut J σ t v) *
        (hermitianTorusPSU J hJ k * weyl J hJ) := by
    rw [oppositeCoordinateAut_spec, oppositeRoot_apply, weyl_inv, map_mul,
      map_mul, hk, hu]
  apply Subtype.ext
  apply Prod.ext
  · have hv := opposite_image_first J hJ k (scaledFieldCoordAut J σ t v)
      (oppositeCoordinateAut J hJ b hV v) himage
    rw [scaledFieldCoordAut_fst, hscale] at hv
    have hv' : J.conj (t : E) * (oppositeCoordinateAut J hJ b hV v).val.1 = σ v.val.1 := by
      apply mul_left_cancel₀ (Units.ne_zero t)
      apply mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero k))
      simpa only [mul_assoc] using hv
    rw [scaledFieldCoordAut_fst]
    simp only [Units.val_inv_eq_inv_val, Units.coe_map]
    change _ = (J.conj (t : E))⁻¹ * σ v.val.1
    rw [← hv', ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero J.conj).mpr (Units.ne_zero t)), one_mul]
  · have hv := opposite_image_second J hJ k (scaledFieldCoordAut J σ t v)
      (oppositeCoordinateAut J hJ b hV v) himage
    rw [scaledFieldCoordAut_snd, hscale] at hv
    have hv' : ((t : E) * J.conj (t : E)) *
        (oppositeCoordinateAut J hJ b hV v).val.2 = σ v.val.2 := by
      apply mul_left_cancel₀
        (mul_ne_zero (pow_ne_zero 4 (Units.ne_zero k))
          (mul_ne_zero (Units.ne_zero t) ((map_ne_zero J.conj).mpr (Units.ne_zero t))))
      linear_combination hv
    rw [scaledFieldCoordAut_snd]
    simp only [Units.val_inv_eq_inv_val, Units.coe_map]
    change _ = (J.conj (t : E))⁻¹ * J.conj ((J.conj (t : E))⁻¹) * σ v.val.2
    rw [map_inv₀, J.conj_involutive, ← hv']
    field_simp

/-- The common first coordinate, torus and Weyl-coset normalizations give
one genuine unitary representative for both root formulas. -/
theorem root_formulas_of_first_normalization [Finite E] [CharP E 2]
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) (hq : 2 < q)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hV : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ)
    (hT : (rootTorus J hJ).map b.toMonoidHom = rootTorus J hJ)
    (hw : ∃ k : Eˣ, b (weyl J hJ) = hermitianTorusPSU J hJ k * weyl J hJ)
    (σ : E ≃+* E) (t : Eˣ)
    (hfirst : ∀ z : hermitianUnipotentCoord J,
      (rootCoordinateAut J hJ b hU z).val.1 = (t : E) * σ z.val.1) :
    (∀ z : hermitianUnipotentCoord J,
      (b (root J hJ z)).val = ProjGenLinGroup.mk (diagonalUnitary J hJ t).val *
        ProjGenLinGroup.map σ.toRingHom (root J hJ z).val *
        (ProjGenLinGroup.mk (diagonalUnitary J hJ t).val)⁻¹) ∧
    (∀ z : hermitianUnipotentCoord J,
      (b (oppositeRoot J hJ z)).val = ProjGenLinGroup.mk (diagonalUnitary J hJ t).val *
        ProjGenLinGroup.map σ.toRingHom (oppositeRoot J hJ z).val *
        (ProjGenLinGroup.mk (diagonalUnitary J hJ t).val)⁻¹) := by
  have hu := coordAut_eq_scaledField_of_first J hcard hfixed hJ hq
    (rootCoordinateAut J hJ b hU) σ t hfirst
    (rootCoordinateAut_torus_intertwining J hJ b hU hT)
  have hv := oppositeCoordinateAut_eq_scaled_of_root_first J hJ hcard hfixed hq
    b hU hV hT hw σ t hfirst
  constructor
  · intro z
    rw [← rootCoordinateAut_spec J hJ b hU z, hu]
    exact scaledFieldCoordAut_root J hJ σ t z
  · intro z
    rw [← oppositeCoordinateAut_spec J hJ b hV z, hv]
    exact scaledFieldCoordAut_opposite J hJ σ t z

end BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
