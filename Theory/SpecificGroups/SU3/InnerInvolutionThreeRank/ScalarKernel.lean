module

public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Involutions and their centralizers through a central kernel of exponent three

Cubing any lift of a projective involution produces an involution lift.
A commutation defect for such a lift is central, has cube one, and has
square one, so it vanishes. Thus the entire centralizer lifts.

This is the scalar-kernel step for SU₃ → PSU₃ in Aschbacher–Smith,
A.3.21(a), printed p.55, as used in the inspection in E.6.18, printed p.252.
-/

public section

open Subgroup
namespace Matrix.SU3.InnerThreeRank
variable {G H : Type*} [Group G] [Group H]

/-- Cubing a lift removes a kernel of exponent three. -/
theorem exists_involution_lift_of_cube_kernel (f : G →* H)
    (hf : Function.Surjective f) (hker : ∀ x ∈ f.ker, x ^ 3 = 1)
    (k : H) (hk : orderOf k = 2) :
    ∃ z : G, orderOf z = 2 ∧ f z = k := by
  obtain ⟨x, rfl⟩ := hf k
  have hx2 : f x ^ 2 = 1 := hk ▸ pow_orderOf_eq_one (f x)
  have hx6 := hker (x ^ 2) (by simp only [MonoidHom.mem_ker, map_pow, hx2])
  have hx3 : f (x ^ 3) = f x := by
    rw [map_pow, pow_succ, hx2, one_mul]
  refine ⟨x ^ 3, orderOf_eq_prime ?_ ?_, hx3⟩
  · simpa only [← pow_mul] using hx6
  · intro he
    have hk1 : f x = 1 := by rw [← hx3, he, map_one]
    simp only [hk1, orderOf_one] at hk
    omega

/-- The centralizer of an involution maps onto the full quotient centralizer. -/
theorem map_centralizer_of_central_cube_kernel (f : G →* H)
    (hf : Function.Surjective f) (hcentral : f.ker ≤ center G)
    (hker : ∀ x ∈ f.ker, x ^ 3 = 1) (z : G) (hz : z ^ 2 = 1) :
    (centralizer ({z} : Set G)).map f = centralizer ({f z} : Set H) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hx)
  · intro y hy
    obtain ⟨x, rfl⟩ := hf y
    let a := x * z * x⁻¹
    let c := a * z⁻¹
    have hcz : c * z = a := by simp [c]
    have hcm : c ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have hc := mem_centralizer_singleton_iff.mp hy
      dsimp [c, a]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      simp only [mul_inv_cancel_right, mul_inv_cancel]
    have hcomm : Commute c z := (mem_center_iff.mp (hcentral hcm) z).symm
    have ha : a ^ 2 = 1 := by
      dsimp [a]
      simpa only [map_pow, map_one, MulAut.conj_apply] using congrArg (MulAut.conj x) hz
    have hc2 : c ^ 2 = 1 := by
      have h := hcomm.mul_pow 2
      rw [hcz, ha, hz, mul_one] at h
      exact h.symm
    have hc1 : c = 1 := by
      have h := hker c hcm
      rwa [pow_succ, hc2, one_mul] at h
    refine ⟨x, ?_, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have haz : a = z := by rw [← hcz, hc1, one_mul]
    exact mul_inv_eq_iff_eq_mul.mp haz

end Matrix.SU3.InnerThreeRank
