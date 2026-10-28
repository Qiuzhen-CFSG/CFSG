module
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
/-!
# Centralizers of inner involutions over M₂₂

An inner automorphism of order two gives an actual involution in the
central quotient. Its native M₂₂ centralizer has order 384, hence is
solvable by the two-and-three case of Burnside's theorem. Pulling it back
through the central kernel proves solvability of the original centralizer.
The quotient equivalence and the inner automorphism are retained explicitly.

Source application: Aschbacher–Smith, proof of 12.6.26, printed p.832.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Sporadic.Mathieu
/-- A nontrivial inner involution over the native M₂₂ has solvable centralizer. -/
theorem centralizer_isSolvable_of_inner_involution
    {B : Type*} [Group B] [Finite B]
    (e : (B ⧸ center B) ≃* M22) (b : B) (hb : orderOf (MulAut.conj b) = 2) :
    Group.IsSolvable (centralizer ({b} : Set B)) := by
  let q : B →* M22 := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hk : q.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hq2 : q b ^ 2 = 1 := by
    rw [←map_pow]
    change b ^ 2 ∈ q.ker
    rw [hk]
    apply mem_center_iff.mpr
    intro x
    have hh := congrArg (fun f : MulAut B => f x) (pow_orderOf_eq_one (MulAut.conj b))
    rw [hb,←map_pow] at hh
    change b ^ 2 * x * (b ^ 2)⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hq1 : q b ≠ 1 := by
    intro hh
    have hz : b ∈ center B := hk ▸ (show b ∈ q.ker from hh)
    have he : MulAut.conj b = 1 := by
      ext x
      change b*x*b⁻¹ = x
      rw [←mem_center_iff.mp hz x,mul_inv_cancel_right]
    rw [he,orderOf_one] at hb
    contradiction
  have ho : orderOf (q b) = 2 := orderOf_eq_prime hq2 hq1
  let C := centralizer ({q b} : Set M22)
  let : Group.IsSolvable C := isSolvable_of_prime_dvd_card_eq_two_or_three C (by
    intro p hp hd
    have hc : Nat.card C = 2 ^ 7 * 3 :=
      (M22FourNormalizers.involution_centralizer_card (q b) ho).trans (by norm_num)
    rw [hc] at hd
    rcases hp.dvd_mul.mp hd with h|h
    · exact Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 2)).mp (hp.dvd_of_dvd_pow h)).resolve_left hp.ne_one)
    · exact Or.inr ((Nat.dvd_prime (by decide)).mp h |>.resolve_left hp.ne_one))
  let : Group.IsSolvable q.ker := by rw [hk]; infer_instance
  let : Group.IsSolvable (C.comap q) := isSolvable_comap_of_solvable_ker q C
  have hle : centralizer ({b} : Set B) ≤ C.comap q := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    change q x * q b = q b * q x
    simpa only [map_mul] using congrArg q (mem_centralizer_singleton_iff.mp hx)
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
end Sporadic.Mathieu

