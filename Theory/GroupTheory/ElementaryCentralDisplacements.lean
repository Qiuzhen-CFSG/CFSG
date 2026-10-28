module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Elementary central displacements

Suppose K moves V only into an elementary subgroup A centralized by V.
Conjugation then fixes every square in V. If C_V(K)=1 all squares vanish,
so V is elementary abelian. No finiteness or coprime action is required.

Source application: Aschbacher–Smith C.1.35, printed p.138, for the
centralizer of the chosen elementary lift in the larger two-core.
-/


public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- Central elementary displacements and a trivial actor centralizer force
the original group to be elementary abelian. -/
theorem elementary_of_central_displacements (V A K : Subgroup G)
    [IsElementaryAbelian 2 A] (hVA : V ≤ centralizer (A : Set G))
    (hd : ⁅K,V⁆ ≤ A) (hc : V ⊓ centralizer (K : Set G) = ⊥) :
    IsElementaryAbelian 2 V := by
  have hpow (v : V) : v^2 = 1 := by
    have hv2 : (v : G)^2 ∈ centralizer (K : Set G) := by
      apply mem_centralizer_iff.mpr
      intro k hk
      let a := k * (v : G) * k⁻¹ * (v : G)⁻¹
      have ha : a ∈ A := hd (commutator_mem_commutator hk v.property)
      have ha2 : a^2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
      have hav : Commute a (v : G) := mem_centralizer_iff.mp (hVA v.property) a ha
      have he : k * (v : G) * k⁻¹ = a * v := by dsimp [a]; group
      have he2 : k * (v : G)^2 * k⁻¹ = (v : G)^2 := by
        calc
          k * (v : G)^2 * k⁻¹ = (k * (v : G) * k⁻¹)^2 := by simp only [pow_two]; group
          _ = (a * v)^2 := by rw [he]
          _ = (v : G)^2 := by rw [hav.mul_pow,ha2,one_mul]
      have hh := congrArg (fun z : G => z*k) he2
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
    exact Subtype.ext (mem_bot.mp (hc.le ⟨V.pow_mem v.property 2,hv2⟩))
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_iff_pow_eq_one.mpr (hpow x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
end Subgroup
