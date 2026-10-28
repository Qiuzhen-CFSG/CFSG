module
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry
public import Theory.LinearAlgebra.QuadraticHyperplaneStabilizer

/-!
# Odd similitudes of the four-dimensional Hermitian determinant form

A similitude fixing a three-dimensional space fixes a nonsingular vector,
since totally singular subspaces of this minus form have dimension at most
one. Its multiplier is therefore one. A nonidentity isometry fixing a
hyperplane has square one, which is incompatible with odd order.

This supplies the orthogonal calculation used in Aschbacher–Smith H.4.4(4),
printed p.381, in the proof of 8.2.3 on p.716.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
namespace Representation.OrthogonalFourMinus.FiniteModel
variable (n : ℕ) [NeZero n]

/-- An odd similitude of the actual minus determinant form cannot have
a three-dimensional fixed space. -/
theorem no_three_dimensional_fixed_similitude
    (t : Space n ≃ₗ[fixedField n] Space n) (c : fixedField n)
    (hs : ∀ v, form n (t v) = c * form n v) (ho : Odd (orderOf t))
    (hfix : finrank (fixedField n) (LinearMap.ker (t.toLinearMap - LinearMap.id)) = 3) : False := by
  let W := LinearMap.ker (t.toLinearMap - LinearMap.id)
  have hc : c = 1 := by
    by_contra hc
    have hz (v : Space n) (hv : v ∈ W) : form n v = 0 := by
      have htv : t v = v := sub_eq_zero.mp hv
      have hh := hs v
      rw [htv] at hh
      apply (mul_eq_zero.mp (show (c-1) * form n v = 0 by linear_combination -hh)).resolve_left
      exact sub_ne_zero.mpr hc
    have hh := singular_finrank_le_one n W hz
    change finrank (fixedField n) W = 3 at hfix
    omega
  have ht (v : Space n) : form n (t v) = form n v := by simpa only [hc,one_mul] using hs v
  have hr : finrank (fixedField n) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1 := by
    have hh := (t.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
    rw [hfix,finrank_space n] at hh
    omega
  have hne : t ≠ 1 := by
    intro he
    have hw : LinearMap.ker (t.toLinearMap - LinearMap.id) = ⊤ := by
      apply top_unique
      intro v hv
      change t v - v = 0
      rw [he]
      exact sub_self v
    rw [hw,finrank_top,finrank_space n] at hfix
    omega
  have ht2 : t^2 = 1 := by
    rcases (form n).eq_one_or_eq_of_fixed_rank_one (form_nonsingular n).1 t (t^2)
      ht (fun v => by simp only [pow_two,LinearEquiv.mul_apply,ht]) hr hne
      (fun v hv => by simp only [pow_two,LinearEquiv.mul_apply,hv]) with hh | hh
    · exact hh
    · have h1 : t*t = t*1 := by simpa only [pow_two,mul_one] using hh
      exact (hne (mul_left_cancel h1)).elim
  have hd : orderOf t ∣ 1 := by
    simpa only [ho.coprime_two_right.gcd_eq_one] using
      Nat.dvd_gcd (dvd_refl (orderOf t)) (orderOf_dvd_of_pow_eq_one ht2)
  exact hne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))
end Representation.OrthogonalFourMinus.FiniteModel


end
