module
public import Theory.GroupTheory.CenterlessSupplementCentralizer
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Two inner component actions determine an element of the product

For commuting subgroups with trivial joint centralizer, the intersection
of their inner-action supplements is their product. Cancel the two inner
representatives; the remainder centralizes both factors and is trivial.

Source application: Aschbacher–Smith E.2.7, printed p.219, paired placement.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {H : Type*} [Group H]
theorem inf_inner_centralizer_supplements_le_sup (K D : Subgroup H)
    (hc : ⁅K,D⁆ = ⊥) (hz : centralizer ((K ⊔ D : Subgroup H) : Set H) = ⊥) :
    (K ⊔ centralizer (K : Set H)) ⊓ (D ⊔ centralizer (D : Set H)) ≤ K ⊔ D := by
  intro x hx
  have hprod (A : Subgroup H) (h : x ∈ A ⊔ centralizer (A : Set H)) :
      ∃a∈A, ∃c∈centralizer (A:Set H), a*c=x := by
    have hh : x ∈ (A : Set H) * (centralizer (A : Set H) : Set H) := by
      rw [← coe_mul_of_right_le_normalizer_left A (centralizer (A : Set H)) (centralizer_le_normalizer _)]
      exact h
    exact hh
  obtain ⟨k,hk,c,hcK,hkc⟩ := hprod K hx.1
  obtain ⟨d,hd,b,hbD,hdb⟩ := hprod D hx.2
  have hKD : K ≤ centralizer (D:Set H) := commutator_eq_bot_iff_le_centralizer.mp hc
  have hDK : D ≤ centralizer (K:Set H) := le_centralizer_iff.mp hKD
  have huK : k⁻¹*x*d⁻¹ ∈ centralizer (K:Set H) := by
    rw [← hkc,inv_mul_cancel_left]
    exact mul_mem hcK (inv_mem (hDK hd))
  have huD : k⁻¹*x*d⁻¹ ∈ centralizer (D:Set H) := by
    rw [← hdb]
    have he : k⁻¹*(d*b)*d⁻¹ = k⁻¹*b := by
      rw [hbD d hd]
      group
    rw [he]
    exact mul_mem (inv_mem (hKD hk)) hbD
  have hu : k⁻¹*x*d⁻¹=1 := by
    apply mem_bot.mp
    rw [← hz]
    have hK : K ≤ centralizer ({k⁻¹*x*d⁻¹} : Set H) := by
      intro y hy
      apply mem_centralizer_iff.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact (huK y hy).symm
    have hD : D ≤ centralizer ({k⁻¹*x*d⁻¹} : Set H) := by
      intro y hy
      apply mem_centralizer_iff.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact (huD y hy).symm
    intro y hy
    exact (((sup_le hK hD) hy) _ (Set.mem_singleton _)).symm
  have he : x=k*d := by
    have hh := congrArg (fun z => k*z*d) hu
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_right,mul_one,inv_mul_cancel] using hh
  rw [he]
  exact mul_mem_sup hk hd
end Subgroup
