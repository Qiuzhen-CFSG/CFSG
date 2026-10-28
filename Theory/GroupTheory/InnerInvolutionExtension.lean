module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.OrderOfElement
public import Theory.GroupAction.AutomorphismFixedTransport
/-!
# An inner action extended by an involution

For a faithful action extending the inner action of a normal subgroup,
coverage by inner automorphisms and a two-element actor gives an actual
outer involution lift and index two. Its centralizer has the same index
as its restriction to the normal subgroup. These retain the literal maps
needed for the quadratic PSL₂ source obstruction.
-/

public section
open Subgroup
namespace Subgroup
/-- A proper inner-by-two extension contains a literal pure-actor involution. -/
theorem exists_outer_involution_of_inner_times_two_action
    {H X A : Type*} [Group H] [Finite H] [Group X] [Group A] [Finite A]
    (K : Subgroup H) [K.Normal] (e : K ≃* X)
    (q : H →* MulAut X) (hq : Function.Injective q)
    (he : ∀ k : K, q (k : H) = MulAut.conj (e k))
    (f : A →* MulAut X) (hc : Nat.card A = 2)
    (hcover : ∀ h : H, ∃ x : X, ∃ a : A, q h = MulAut.conj x * f a)
    (hK : K ≠ ⊤) :
    ∃ a : H, a ∉ K ∧ a ^ 2 = 1 ∧ K.index = 2 ∧
      ∃ σ : A, orderOf σ = 2 ∧ q a = f σ := by
  classical
  obtain ⟨h, hh⟩ : ∃ h : H, h ∉ K := by
    by_contra! hh
    exact hK (top_unique (fun h _ => hh h))
  obtain ⟨x, σ, hs⟩ := hcover h
  let k : K := e.symm x
  let a := (k : H)⁻¹ * h
  have haK : a ∉ K := by
    intro ha
    have hh' := K.mul_mem k.property ha
    have hc : (k : H) * a = h := by dsimp [a]; group
    exact hh (hc ▸ hh')
  have hqa : q a = f σ := by
    change q ((k : H)⁻¹ * h) = _
    rw [map_mul, map_inv, he, hs]
    simp only [k, e.apply_symm_apply, inv_mul_cancel_left]
  have hσ : σ ≠ 1 := by
    intro heq
    have ha1 : a = 1 := hq (by rw [hqa, heq, map_one, map_one])
    exact haK (ha1 ▸ K.one_mem)
  have hσord : orderOf σ ∣ 2 := by
    rw [← hc]
    exact _root_.orderOf_dvd_natCard (x := σ)
  have hσ2 : σ ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hσord
  have ha2 : a ^ 2 = 1 := hq (by rw [map_pow, hqa, ← map_pow, hσ2, map_one, map_one])
  have hcases : ∀ τ : A, τ = 1 ∨ τ = σ := by
    obtain ⟨b, hb, hu⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
    intro τ
    by_cases hτ : τ = 1
    · exact .inl hτ
    · exact .inr ((hu τ hτ).trans (hu σ hσ).symm)
  have hi : K.index = 2 := by
    apply index_eq_two_iff_exists_notMem_and.mpr
    refine ⟨a, haK, ?_⟩
    intro g
    obtain ⟨y, τ, hg⟩ := hcover g
    let l : K := e.symm y
    have hql : q (l : H) = MulAut.conj y := by rw [he]; simp only [l, e.apply_symm_apply]
    rcases hcases τ with hτ | hτ
    · right
      have hgl : g = (l : H) := hq (by rw [hg, hτ, map_one, mul_one, hql])
      exact hgl ▸ l.property
    · left
      have hgl : g * a = (l : H) := hq (by
        rw [map_mul, hg, hτ, hqa, hql, mul_assoc, ← map_mul, ← pow_two, hσ2, map_one, mul_one])
      exact hgl ▸ l.property
  exact ⟨a, haK, ha2, hi, σ, orderOf_eq_prime hσ2 hσ, hqa⟩
end Subgroup

namespace Subgroup
/-- An outer involution centralizer preserves its index on an index-two subgroup. -/
theorem centralizer_index_eq_restriction_of_index_two
    {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal] (hK : K.index = 2)
    (a : H) (ha : a ∉ K) :
    (centralizer ({a} : Set H)).index = ((centralizer ({a} : Set H)).subgroupOf K).index := by
  let C := centralizer ({a} : Set H)
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hr : K.relIndex C = 2 := by
    have hd : K.relIndex C ∣ 2 := hK ▸ relIndex_dvd_index_of_normal K C
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hd | hd
    · have hh : C ≤ K := relIndex_eq_one.mp hd
      exact (ha (hh haC)).elim
    · exact hd
  have h1 := relIndex_inf_mul_relIndex C K (⊤ : Subgroup H)
  have h2 := relIndex_inf_mul_relIndex K C (⊤ : Subgroup H)
  simp only [inf_top_eq, relIndex_top_right, hK, hr] at h1 h2
  rw [inf_comm K C] at h2
  change C.index = C.relIndex K
  omega
end Subgroup
