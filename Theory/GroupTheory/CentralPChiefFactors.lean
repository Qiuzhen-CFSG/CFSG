module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Central p-chief factors

The predicate quantifies over actual normal intervals K < L in H with no
intermediate H-normal subgroup. The p-group test uses the relative quotient
`L / (K.subgroupOf L)`. Centrality says the image of L lies in the center of
`H / K`; equivalently [H,L] ≤ K. Neither normality in a larger ambient group
nor a conclusion about O_p(H) is included in this hypothesis.

Source: the chief-factor convention in Aschbacher–Smith, *The Classification
of Quasithin Groups*, B.7.2, printed p. 119. That application uses p = 2 and
separately assumes H = O²(H).
-/

@[expose] public section

namespace Subgroup
variable {H : Type*} [Group H]

/-- Every normal interval with a nontrivial p-group chief quotient is central. -/
def HasCentralPChiefFactors (p : ℕ) (H : Type*) [Group H] : Prop :=
  ∀ (K L : Subgroup H) (_ : K.Normal) (_ : L.Normal), K < L →
    (∀ N : Subgroup H, N.Normal → K ≤ N → N ≤ L → N = K ∨ N = L) →
    IsPGroup p (L ⧸ K.subgroupOf L) →
    L.map (QuotientGroup.mk' K) ≤ center (H ⧸ K)

open scoped commutatorElement

/-- Centrality of the image of L in H/K is precisely [H,L] ≤ K. -/
theorem map_mk_le_center_iff (K L : Subgroup H) [K.Normal] :
    L.map (QuotientGroup.mk' K) ≤ center (H ⧸ K) ↔ ⁅(⊤ : Subgroup H), L⁆ ≤ K := by
  rw [commutator_le]
  constructor
  · intro h x hx y hy
    have hc := mem_center_iff.mp (h (mem_map_of_mem (QuotientGroup.mk' K) hy))
      (QuotientGroup.mk' K x)
    have he : QuotientGroup.mk' K ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc
    exact (QuotientGroup.eq_one_iff _).mp he
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := hz
    apply mem_center_iff.mpr
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    have he : QuotientGroup.mk' K ⁅x, y⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (h x (mem_top x) y hy)
    rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at he

/-- A central p-chief-factor hypothesis yields its concrete commutator containment. -/
theorem HasCentralPChiefFactors.commutator_le {p : ℕ}
    (h : HasCentralPChiefFactors p H)
    (K L : Subgroup H) [K.Normal] [L.Normal] (hlt : K < L)
    (hchief : ∀ N : Subgroup H, N.Normal → K ≤ N → N ≤ L → N = K ∨ N = L)
    (hp : IsPGroup p (L ⧸ K.subgroupOf L)) : ⁅(⊤ : Subgroup H), L⁆ ≤ K :=
  (map_mk_le_center_iff K L).mp (h K L inferInstance inferInstance hlt hchief hp)
end Subgroup
