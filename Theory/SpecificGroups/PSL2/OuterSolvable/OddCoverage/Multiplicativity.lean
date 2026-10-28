module

public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.RootParameters
public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.RootGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Recovering field multiplication from the projective root action

The diagonal torus acts on the upper root group by square scalars. Apply an
arbitrary root-preserving automorphism to this action and lift the image of a
torus element. Since parameter one is fixed, the image normalizes the upper
root group and its action is again multiplication by a square scalar. This
forces the additive root-coordinate equivalence to respect square multiples.
In characteristic different from two every scalar is a difference of squares,
which recovers multiplication on the entire field.

This proves the field-recovery step of the A₁ automorphism theorem in GLS3,
Theorem 2.5.12 and §2.7, directly on the central quotient. It does not need
finiteness or an automorphism-lifting theorem.
-/

namespace Theory.PSL2.OuterSolvable.OddCoverage
variable {K : Type*} [Field K]

private theorem rootParameter_mul_unit_sq (hchar : ringChar K ≠ 2)
    (b : MulAut (Group K)) (hU : (rootGroup K).map b.toMonoidHom = rootGroup K)
    (h1 : b (upper 1) = upper 1) (r : Kˣ) (t : K) :
    rootParameter b hU ((r : K) ^ 2 * t) =
      rootParameter b hU ((r : K) ^ 2) * rootParameter b hU t := by
  have hrel (s : K) : torus r * upper s * (torus r)⁻¹ = upper ((r : K) ^ 2 * s) :=
    conj_upper_of_lowerLeft_zero (slTorus r) rfl s
  obtain ⟨A, hA⟩ := quotientMap_surjective K (b (torus r))
  have hmap (s : K) : quotientMap K A * upper (rootParameter b hU s) *
      (quotientMap K A)⁻¹ = upper (rootParameter b hU ((r : K) ^ 2 * s)) := by
    have he := congrArg b (hrel s)
    simpa only [map_mul, map_inv, map_upper b hU, ← hA] using he
  have hf1 := rootParameter_one_of_fixed b hU h1
  have hc : A.val 1 0 = 0 := by
    apply lowerLeft_zero_of_conj_upper hchar A (rootParameter b hU ((r : K) ^ 2))
    simpa only [hf1, mul_one] using hmap 1
  have hs (s : K) : rootParameter b hU ((r : K) ^ 2 * s) =
      A.val 0 0 ^ 2 * rootParameter b hU s :=
    upper_injective ((hmap s).symm.trans (conj_upper_of_lowerLeft_zero A hc _))
  have hr : rootParameter b hU ((r : K) ^ 2) = A.val 0 0 ^ 2 := by
    simpa only [hf1, mul_one] using hs 1
  rw [hs, hr]

public theorem rootParameter_mul (hchar : ringChar K ≠ 2)
    (b : MulAut (Group K)) (hU : (rootGroup K).map b.toMonoidHom = rootGroup K)
    (h1 : b (upper 1) = upper 1) (s t : K) :
    rootParameter b hU (s * t) = rootParameter b hU s * rootParameter b hU t := by
  let f := rootParameterEquiv b hU
  have hsq (r t : K) : f (r ^ 2 * t) = f (r ^ 2) * f t := by
    by_cases hr : r = 0
    · simp [hr]
    · exact rootParameter_mul_unit_sq hchar b hU h1 (Units.mk0 r hr) t
  let r := (s + 1) / 2
  let v := (s - 1) / 2
  have hs : s = r ^ 2 - v ^ 2 := by
    dsimp [r, v]
    field_simp [Ring.two_ne_zero hchar]
    ring
  change f (s * t) = f s * f t
  calc
    f (s * t) = f (r ^ 2 * t - v ^ 2 * t) := by rw [hs, sub_mul]
    _ = f (r ^ 2 * t) - f (v ^ 2 * t) := f.map_sub _ _
    _ = (f (r ^ 2) - f (v ^ 2)) * f t := by rw [hsq, hsq, sub_mul]
    _ = f s * f t := by rw [← f.map_sub, ← hs]

end Theory.PSL2.OuterSolvable.OddCoverage
