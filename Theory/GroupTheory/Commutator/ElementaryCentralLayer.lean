module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Elementary central quotients of full commutators

Suppose U equals its commutator with E, the commutator subgroup of U lies
in a normal subgroup Z, and E centralizes every square of an element of U.
Then the image of U in G/Z is elementary abelian at two. No finiteness or
coprimality hypothesis is needed.

The quotient image of U is abelian, so its squaring map is a homomorphism.
For u in U and e in E, the two factors of the commutator commute modulo Z;
its square is trivial because e fixes u². Thus every generating commutator
lies in the kernel of the squaring map, and so does all of U's image.

This supplies the elementary quotient-module step for the maximal V₁
construction before (9.1)(10) in Stellmacher, Journal of Algebra 190 (1997),
p.47; the finite-group and graph inputs belong to its caller.
-/

namespace Subgroup
open scoped commutatorElement

/-- A full commutator subgroup becomes elementary abelian modulo its derived
subgroup if the actors fix all of its squares. -/
public theorem elementaryAbelian_quotient_image_of_commutator_eq
    {G : Type*} [Group G] (U E Z : Subgroup G) [Z.Normal]
    (hderived : ⁅U, U⁆ ≤ Z) (hfull : ⁅U, E⁆ = U)
    (hsquares : ∀ u ∈ U, u ^ 2 ∈ centralizer (E : Set G)) :
    IsElementaryAbelian 2 (U.map (QuotientGroup.mk' Z)) := by
  let q := QuotientGroup.mk' Z
  let V := U.map q
  let A := E.map q
  have hVV : ⁅V, V⁆ = ⊥ := by
    rw [← map_commutator]
    exact (map_eq_bot_iff (f := q) _).mpr (by simpa [q] using hderived)
  let _ : IsMulCommutative V := commutator_self_eq_bot_iff.mp hVV
  let _ : CommGroup V := IsMulCommutative.instCommGroup
  let K := (powMonoidHom 2 : V →* V).ker.map V.subtype
  have hnorm : E ≤ normalizer (U : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hfull.le
  have hVA : ⁅V, A⁆ = V := by
    rw [← map_commutator, hfull]
  have hVK : V ≤ K := by
    rw [← hVA]
    apply commutator_le.mpr
    rintro a ⟨u, hu, rfl⟩ b ⟨e, he, rfl⟩
    have hconj : e * u⁻¹ * e⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (hnorm he) u⁻¹).mp (U.inv_mem hu)
    have hcomm : Commute (q u) (q (e * u⁻¹ * e⁻¹)) := by
      change q u * q (e * u⁻¹ * e⁻¹) = q (e * u⁻¹ * e⁻¹) * q u
      exact congrArg Subtype.val (mul_comm
        (⟨q u, mem_map_of_mem q hu⟩ : V) ⟨q (e * u⁻¹ * e⁻¹), mem_map_of_mem q hconj⟩)
    have hfix : e * (u ^ 2)⁻¹ * e⁻¹ = (u ^ 2)⁻¹ := by
      have hc : Commute e (u ^ 2) := mem_centralizer_iff.mp (hsquares u hu) e he
      rw [hc.inv_right.eq, mul_inv_cancel_right]
    have hconjpow : (e * u⁻¹ * e⁻¹) ^ 2 = e * (u ^ 2)⁻¹ * e⁻¹ := by
      simp [pow_two, mul_assoc]
    have hpow : (⁅q u, q e⁆) ^ 2 = 1 := by
      calc
        (⁅q u, q e⁆) ^ 2 = (q u * q (e * u⁻¹ * e⁻¹)) ^ 2 := by
          simp only [commutatorElement_def, map_mul, map_inv, mul_assoc]
        _ = (q u) ^ 2 * (q (e * u⁻¹ * e⁻¹)) ^ 2 := hcomm.mul_pow 2
        _ = 1 := by
          rw [← map_pow, ← map_pow, hconjpow, hfix, map_inv, mul_inv_cancel]
    have hm : ⁅q u, q e⁆ ∈ V := hVA ▸
      commutator_mem_commutator (mem_map_of_mem q hu) (mem_map_of_mem q he)
    refine ⟨⟨⁅q u, q e⁆, hm⟩, ?_, rfl⟩
    change (⟨⁅q u, q e⁆, hm⟩ : V) ^ 2 = 1
    exact Subtype.ext hpow
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro v
  obtain ⟨w, hw, heq⟩ := hVK v.property
  have hwv : w = v := Subtype.ext heq
  subst w
  exact hw

end Subgroup
