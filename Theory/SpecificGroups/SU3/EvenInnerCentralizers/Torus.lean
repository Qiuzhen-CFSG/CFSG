module

public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.RootGeneration

/-!
# The actual norm-one torus in projective SU₃

The diagonal matrices have entries `k, k⁻², k` when `conj k = k⁻¹`.
Their projective kernel is exactly the cube roots of unity. Consequently,
when `3 ∣ q+1`, their projective image has order `(q+1)/3`, where `q`
is the fixed-field order. These are the torus and scalar-kernel calculations
in Aschbacher–Smith 16.4.8, printed p.1188, with Huppert II.10.12 coordinates.
-/

public section
open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The actual norm-one subgroup of the matrix field's units. -/
@[expose] def normOne : Subgroup Eˣ where
  carrier := {k | J.conj (k : E) = (k : E)⁻¹}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change J.conj ((a : E) * (b : E)) = ((a : E) * (b : E))⁻¹
    rw [map_mul, ha, hb, mul_inv]
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] using
      congrArg (fun x : E => x⁻¹) ha

/-- The projective norm-one torus homomorphism uses the genuine SU matrices. -/
@[expose] def normOneMap
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    normOne J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (hermitianTorusPSU J hJ).comp (normOne J).subtype

/-- The projective torus is the image, not the unquotiented group of units. -/
@[expose] def normOneImage
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) := (normOneMap J hJ).range

/-- The norm-one condition is the `(q+1)`-st root-of-unity condition. -/
theorem normOne_eq_rootsOfUnity {q : ℕ}
    (hconj : ∀ x : E, J.conj x = x ^ q) :
    normOne J = rootsOfUnity (q + 1) E := by
  ext k
  change (J.conj (k : E) = (k : E)⁻¹) ↔ k ∈ rootsOfUnity (q + 1) E
  rw [mem_rootsOfUnity]
  constructor
  · intro hk
    apply Units.ext
    change (k : E) ^ (q + 1) = 1
    rw [pow_succ, ← hconj, hk, inv_mul_cancel₀ (Units.ne_zero k)]
  · intro hk
    have hv : (k : E) ^ (q + 1) = 1 := congrArg Units.val hk
    rw [pow_succ, ← hconj] at hv
    exact eq_inv_of_mul_eq_one_left hv

/-- The norm-one group has order `q+1`. -/
theorem normOne_card [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ q) : Nat.card (normOne J) = q + 1 := by
  rw [normOne_eq_rootsOfUnity J hconj, rootsOfUnity_eq_ker,
    IsCyclic.card_powMonoidHom_ker, Nat.card_units, hcard]
  apply Nat.gcd_eq_right
  rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by
    simpa [mul_comm] using Nat.sq_sub_sq q 1]
  exact dvd_mul_left _ _

/-- A norm-one torus matrix is projectively trivial exactly when its cube is one. -/
theorem normOneMap_eq_one_iff
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : normOne J) :
    normOneMap J hJ k = 1 ↔ k ^ 3 = 1 := by
  have hk : J.conj (k.val : E) = (k.val : E)⁻¹ := k.property
  constructor
  · intro he
    have hpgl : ProjGenLinGroup.mk (hermitianTorusGL J k.val) = 1 :=
      congrArg Subtype.val he
    have hc : hermitianTorusGL J k.val ∈ Subgroup.center (GL (Fin 3) E) := by
      rw [← ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hpgl
    obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
    have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) hc
    have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hc
    simp [hermitianTorusMatrix, Matrix.scalar_apply, hk] at h11 h22
    have hm : (k.val : E)⁻¹ * (k.val : E)⁻¹ = (k.val : E) := h11.symm.trans h22
    apply Subtype.ext
    apply Units.ext
    change (k.val : E) ^ 3 = 1
    have hh := congrArg (fun a : E => a * (k.val : E) ^ 2) hm
    field_simp at hh
    linear_combination -hh
  · intro he
    have he' : (k.val : E) ^ 3 = 1 := congrArg (fun a : normOne J => (a.val : E)) he
    have hm : (k.val : E)⁻¹ * (k.val : E)⁻¹ = (k.val : E) := by
      field_simp
      linear_combination -he'
    have hscalar : hermitianTorusGL J k.val = GeneralLinearGroup.scalar (Fin 3) k.val := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hermitianTorusMatrix, GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, hk, hm]
    apply Subtype.ext
    change ProjGenLinGroup.mk (hermitianTorusGL J k.val) = 1
    rw [hscalar]
    simp

/-- The projective torus kernel is precisely its cubic power kernel. -/
theorem normOneMap_ker
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (normOneMap J hJ).ker = (powMonoidHom 3 : normOne J →* normOne J).ker := by
  ext k
  exact normOneMap_eq_one_iff J hJ k

/-- The scalar kernel has order `gcd(q+1,3)`. -/
theorem normOneMap_ker_card [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (normOneMap J hJ).ker = Nat.gcd (q + 1) 3 := by
  rw [normOneMap_ker, IsCyclic.card_powMonoidHom_ker, normOne_card J hcard hconj]

/-- The projective norm-one torus has the exact quotient order. -/
theorem normOneImage_card [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (normOneImage J hJ) = (q + 1) / Nat.gcd (q + 1) 3 := by
  have h := (normOneMap J hJ).ker.card_mul_index
  rw [Subgroup.index_ker, normOneMap_ker_card J hcard hconj,
    normOne_card J hcard hconj] at h
  exact Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt (Nat.gcd_pos_of_pos_right (q + 1) (by decide : 0 < 3))) (by
    simpa only [normOneImage, mul_comm] using h)

/-- The exact unitary congruence gives the denominator three from the source. -/
theorem normOneImage_card_binary [Finite E] {n : ℕ}
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hmod : 2 ^ n % 3 = 2) :
    Nat.card (normOneImage J hJ) = (2 ^ n + 1) / 3 := by
  rw [normOneImage_card J hcard hconj hJ,
    Nat.gcd_eq_right (show 3 ∣ 2 ^ n + 1 from Nat.dvd_of_mod_eq_zero (by omega))]

end BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
