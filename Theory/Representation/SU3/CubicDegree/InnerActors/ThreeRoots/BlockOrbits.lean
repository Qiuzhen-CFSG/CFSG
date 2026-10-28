module

public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots.Coordinates

/-!
# The two fixed-field block orbits of isotropic lines

Every nonzero isotropic vector for the standard antidiagonal Hermitian form
is a nonzero scalar multiple of either the first column of an actual
fixed-field SL₂ block or that block applied to `(b,1,1)`, where the trace of
`b` is one. No finiteness or field-order hypothesis is needed.

If the middle coordinate vanishes, isotropy makes the ratio of the outer
coordinates fixed by conjugation. Otherwise normalize the middle coordinate
to one and write the vector as `(x,1,z)`. The traces `r = x + conj x` and
`t = z + conj z`, together with `α = x + b*r` and `δ = z + b*t`, are fixed;
isotropy gives `r*δ - α*t = 1`. Thus `[[r,α],[t,δ]]` is the required SL₂
matrix, and its actual SU₃ block sends `(b,1,1)` to `(x,1,z)`.

This discharges the coordinate premise of
`ThreeRoots.standard_generation_of_block_orbits` and
`ThreeRoots.generation_of_block_orbits`. The coordinate conventions are
Huppert II.10.12; the consuming unitary argument is Aschbacher--Smith K.3.3,
printed p.456 of the combined manuscript of 1 March 2004.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open HermitianForm.BorelTorus.EvenCenterAction
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 3 F)

private theorem remainder_fixed (b : F) (hb : b + J.conj b = 1) (x : F) :
    J.conj (x + b * (x + J.conj x)) = x + b * (x + J.conj x) := by
  have hcb : J.conj b = 1 - b := eq_sub_of_add_eq' hb
  rw [map_add, map_mul, map_add, J.conj_involutive, hcb]
  simp only [CharTwo.sub_eq_add]
  ring_nf
  simp [CharTwo.two_eq_zero]

private theorem orbit_determinant (x z b : F)
    (hi : J.conj x * z + 1 + J.conj z * x = 0) :
    (x + J.conj x) * (z + b * (z + J.conj z)) -
      (x + b * (x + J.conj x)) * (z + J.conj z) = 1 := by
  have hc : J.conj x * z + J.conj z * x = 1 := by
    apply CharTwo.add_eq_zero.mp
    simpa only [add_assoc, add_left_comm, add_comm] using hi
  calc
    _ = J.conj x * z - J.conj z * x := by ring
    _ = J.conj x * z + J.conj z * x := CharTwo.sub_eq_add _ _
    _ = 1 := hc

omit [CharP F 2] in
private theorem normalize_isotropic (v : Fin 3 → F) (hy : v 1 ≠ 0)
    (hi : J.conj (v 0) * v 2 + J.conj (v 1) * v 1 + J.conj (v 2) * v 0 = 0) :
    J.conj (v 0 / v 1) * (v 2 / v 1) + 1 +
      J.conj (v 2 / v 1) * (v 0 / v 1) = 0 := by
  have hcy : J.conj (v 1) ≠ 0 := (map_ne_zero J.conj).mpr hy
  rw [map_div₀, map_div₀]
  field_simp
  linear_combination hi

private theorem normalized_second_orbit
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (b : F) (hb : b + J.conj b = 1)
    (x z : F) (hi : J.conj x * z + 1 + J.conj z * x = 0) :
    ∃ A : SpecialLinearGroup (Fin 2) (fixedField J),
      (block J hJ A).val.val.mulVec ![b,1,1] = ![x,1,z] := by
  let r : fixedField J := ⟨x + J.conj x, by
    change J.conj (x + J.conj x) = x + J.conj x
    rw [map_add, J.conj_involutive, add_comm]⟩
  let t : fixedField J := ⟨z + J.conj z, by
    change J.conj (z + J.conj z) = z + J.conj z
    rw [map_add, J.conj_involutive, add_comm]⟩
  let α : fixedField J := ⟨x + b * (x + J.conj x), remainder_fixed J b hb x⟩
  let δ : fixedField J := ⟨z + b * (z + J.conj z), remainder_fixed J b hb z⟩
  let A : SpecialLinearGroup (Fin 2) (fixedField J) := ⟨!![r,α;t,δ], by
    rw [Matrix.det_fin_two]
    apply Subtype.ext
    change (x + J.conj x) * (z + b * (z + J.conj z)) -
      (x + b * (x + J.conj x)) * (z + J.conj z) = 1
    exact orbit_determinant J x z b hi⟩
  refine ⟨A, ?_⟩
  rw [block_val]
  ext i
  fin_cases i <;> simp [A, r, t, α, δ, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  all_goals rw [mul_comm, add_left_comm, CharTwo.add_self_eq_zero, add_zero]

/-- Explicit covering by the two fixed-field block orbits of isotropic lines. -/
theorem blockOrbitDecomposition
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (b : F) (hb : b + J.conj b = 1) :
    BlockOrbitDecomposition J hJ b := by
  intro v hv hi
  have hcoord : J.conj (v 0) * v 2 + J.conj (v 1) * v 1 +
      J.conj (v 2) * v 0 = 0 := by
    simpa [hJ, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hi
  by_cases hy : v 1 = 0
  · left
    by_cases hz : v 2 = 0
    · have hx : v 0 ≠ 0 := by
        intro hx
        apply hv
        ext i
        fin_cases i <;> simp [hx, hy, hz]
      refine ⟨1, (v 0)⁻¹, inv_ne_zero hx, ?_⟩
      intro i
      rw [block_val]
      fin_cases i <;> simp [hx, hy, hz]
    · have he : J.conj (v 0) * v 2 = J.conj (v 2) * v 0 := by
        apply CharTwo.add_eq_zero.mp
        simpa [hy] using hcoord
      have hr : J.conj (v 0 / v 2) = v 0 / v 2 := by
        rw [map_div₀]
        apply (div_eq_div_iff ((map_ne_zero J.conj).mpr hz) hz).mpr
        simpa only [mul_comm] using he
      let r : fixedField J := ⟨v 0 / v 2, hr⟩
      let A : SpecialLinearGroup (Fin 2) (fixedField J) := ⟨!![r,1;1,0], by
        simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
      refine ⟨A, (v 2)⁻¹, inv_ne_zero hz, ?_⟩
      intro i
      rw [block_val]
      fin_cases i <;> simp [A, r, hy, hz, div_eq_mul_inv, mul_comm]
  · right
    obtain ⟨A, hA⟩ := normalized_second_orbit J hJ b hb (v 0 / v 1) (v 2 / v 1)
      (normalize_isotropic J v hy hcoord)
    refine ⟨A, (v 1)⁻¹, inv_ne_zero hy, ?_⟩
    intro i
    rw [hA]
    fin_cases i <;> simp [hy, div_eq_mul_inv, mul_comm]

end Representation.SU3.CubicDegree.InnerActors.ThreeRoots
