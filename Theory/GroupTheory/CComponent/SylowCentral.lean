module

public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Sylow-central elements normalize components

The Sylow intersection with a component has a nonidentity element. An element
centralizing the Sylow subgroup fixes that element. If the component and its
conjugate were distinct, their commutation would put the fixed element in the
component's trivial center, a contradiction.

The divisibility hypothesis is explicit, so this reusable p-local argument
does not import the odd-order theorem. The p = 2 application is GLS, Volume 1,
(4.6), used in Volume 4, Chapter 2, Lemma 4.9.
-/

open Subgroup

namespace Subgroup
/-- In a radical-free group, centralizing a Sylow p-subgroup forces normalization
of every C-component whose order is divisible by p. -/
public theorem IsCComponent.mem_normalizer_of_centralizes_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {L : Subgroup G} (hL : L.IsCComponent)
    (hrad : solvableRadical G = ⊥)
    (hdiv : p ∣ Nat.card L) (S : Sylow p G) {z : G}
    (hz : ∀ s : S, Commute z (s : G)) : z ∈ normalizer (L : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  have hconj := hL.map_equiv (MulAut.conj z)
  have hc := hL.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot
    hrad hconj (Ne.symm hne)
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  let : Nontrivial (T : Subgroup L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (T.ne_bot_of_dvd_card hdiv)
  obtain ⟨x, hx, hx1⟩ := (T : Subgroup L).exists_ne_one_of_nontrivial
  have hxS : (x : G) ∈ (S : Subgroup G) := by
    have := hT ▸ hx
    exact this
  have hfix : MulAut.conj z (x : G) = x := by
    change z * (x : G) * z⁻¹ = x
    rw [(hz ⟨x, hxS⟩).eq]
    simp
  have hxconj : (x : G) ∈ L.map (MulAut.conj z).toMonoidHom :=
    hfix ▸ mem_map_of_mem (MulAut.conj z).toMonoidHom x.property
  have hxcenter : x ∈ center L := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact ((commutator_eq_bot_iff_le_centralizer.mp hc y.property) x hxconj).symm
  have hcenter := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hL.subnormal
  exact hx1 (mem_bot.mp (hcenter ▸ hxcenter))
end Subgroup
