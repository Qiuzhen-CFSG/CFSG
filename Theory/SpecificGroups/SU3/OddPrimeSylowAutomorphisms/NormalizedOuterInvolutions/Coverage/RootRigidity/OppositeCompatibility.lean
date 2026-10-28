module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.Coordinates
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.Diagonal
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.FirstField

/-!
# Compatibility of the two Hermitian root parameters

Suppose an automorphism preserves the two opposite root groups and the torus,
fixes the torus element at `-1`, and sends the Weyl element into its torus coset.
An upper first-coordinate formula `t * σ(a)` then forces the opposite formula
`conj(t)⁻¹ * σ(a)`, with the same field automorphism and scalar.

Odd characteristic and equivariance at `-1` first recover the full upper
coordinate map. Apply the explicit Bruhat relation to a coordinate with first
entry one. Comparing the bottom two matrix entries determines the Weyl-image
parameter up to exactly the needed identity
`conj(k) = k² * t * conj(t)`. A second matrix comparison gives the opposite
first coordinate. Both comparisons retain and then cancel the projective
scalar; they require no choice of a lift of the ambient automorphism.

This is the conditional compatibility step in Steinberg, Theorem 36,
steps (4)–(7), `refs/KGroup/GLS3/Chapter2St1.tex`. The torus and Weyl-coset
hypotheses are inputs for the assembly owner to discharge. The argument works
in every odd characteristic, including three, without generation, simplicity,
perfectness, or an involution assumption on the automorphism.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
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

private theorem upper_formula [Finite E]
    (h2 : (2 : E) ≠ 0) (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (ht : b (hermitianTorusPSU J hJ (-1)) = hermitianTorusPSU J hJ (-1))
    (σ : E ≃+* E) (t : Eˣ)
    (hfirst : ∀ z : hermitianUnipotentCoord J,
      (rootCoordinateAut J hJ b hU z).val.1 = (t : E) * σ z.val.1) :
    ∀ z, b (root J hJ z) = root J hJ (scaledFieldCoordAut J σ t z) := by
  have hu : rootCoordinateAut J hJ b hU = scaledFieldCoordAut J σ t :=
    coordAut_ext_of_first J h2 _ _
      (fun z => (hfirst z).trans (scaledFieldCoordAut_fst J σ t z).symm)
      (rootCoordinateAut_neg_equivariant J hJ b hU ht)
      (scaledFieldCoordAut_neg_equivariant J σ t)
  intro z
  rw [← rootCoordinateAut_spec J hJ b hU z, hu]

/-- The upper semilinear parameter determines the opposite parameter under
torus preservation and the explicit Weyl-coset hypothesis. -/
public theorem opposite_first_of_root_first [Finite E]
    (h2 : (2 : E) ≠ 0) (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hV : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ)
    (hT : (rootTorus J hJ).map b.toMonoidHom = rootTorus J hJ)
    (ht : b (hermitianTorusPSU J hJ (-1)) = hermitianTorusPSU J hJ (-1))
    (hw : ∃ k : Eˣ, b (weyl J hJ) = hermitianTorusPSU J hJ k * weyl J hJ)
    (σ : E ≃+* E) (t : Eˣ)
    (hfirst : ∀ z : hermitianUnipotentCoord J,
      (rootCoordinateAut J hJ b hU z).val.1 = (t : E) * σ z.val.1) :
    ∀ z : hermitianUnipotentCoord J,
      (oppositeCoordinateAut J hJ b hV z).val.1 = (J.conj (t : E))⁻¹ * σ z.val.1 := by
  have hu := upper_formula J hJ h2 b hU ht σ t hfirst
  obtain ⟨k, hk⟩ := hw
  obtain ⟨z, hz⟩ := coord_first_surjective J h2 1
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
  intro v
  have hv := opposite_image_first J hJ k (scaledFieldCoordAut J σ t v)
    (oppositeCoordinateAut J hJ b hV v) (by
      rw [oppositeCoordinateAut_spec, oppositeRoot_apply, weyl_inv, map_mul,
        map_mul, hk, hu])
  rw [scaledFieldCoordAut_fst, hscale] at hv
  have hv' : J.conj (t : E) * (oppositeCoordinateAut J hJ b hV v).val.1 = σ v.val.1 := by
    apply mul_left_cancel₀ (Units.ne_zero t)
    apply mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero k))
    simpa only [mul_assoc] using hv
  calc
    _ = (J.conj (t : E))⁻¹ *
        (J.conj (t : E) * (oppositeCoordinateAut J hJ b hV v).val.1) := by
      rw [← mul_assoc, inv_mul_cancel₀ ((map_ne_zero J.conj).mpr (Units.ne_zero t)), one_mul]
    _ = _ := by rw [hv']

/-- The compatibility statement for prime fixed-field order congruent to three
modulo eight. Only the matrix-field cardinality is needed to establish odd
characteristic; no fixed-field cardinality or ambient simplicity is required. -/
public theorem opposite_first_of_prime_square_root_first [Finite E]
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (hcard : Nat.card E = p ^ 2)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hV : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ)
    (hT : (rootTorus J hJ).map b.toMonoidHom = rootTorus J hJ)
    (ht : b (hermitianTorusPSU J hJ (-1)) = hermitianTorusPSU J hJ (-1))
    (hw : ∃ k : Eˣ, b (weyl J hJ) = hermitianTorusPSU J hJ k * weyl J hJ)
    (σ : E ≃+* E) (t : Eˣ)
    (hfirst : ∀ z : hermitianUnipotentCoord J,
      (rootCoordinateAut J hJ b hU z).val.1 = (t : E) * σ z.val.1) :
    ∀ z : hermitianUnipotentCoord J,
      (oppositeCoordinateAut J hJ b hV z).val.1 = (J.conj (t : E))⁻¹ * σ z.val.1 :=
  opposite_first_of_root_first J hJ (two_ne_zero_of_prime_square hp (by omega) hcard)
    b hU hV hT ht hw σ t hfirst

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
