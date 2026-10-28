module
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index


/-!
# Comparing conjugate subgroups modulo a coprime normal section

Let `K ≤ N` be normal subgroups of a finite group, with `N/K` of order
prime to `p`. If `x ∈ N` and both `A` and its conjugate by `x` lie in the
same `p`-subgroup `U`, their images modulo `K` are equal. In particular,
`A ≤ A.conjBy x ⊔ K`.

The image of `U ∩ N` in `N/K` is both a `p`-group and of order prime to
`p`, so `U ∩ N ≤ K`. For `a ∈ A`, the element `(x a x⁻¹) / a` belongs
to this intersection: both factors lie in `U`, and normality of `N` puts
their difference in `N`. Thus `a` and its conjugate have the same quotient
image. The containment follows by taking the inverse image of the subgroup
image equality.

This standard finite-group comparison is used in Stellmacher (9.3),
Journal of Algebra 190 (1997), pp.49–50, with the two-core and the
2,2′-core of the ambient centralizer as the two normal subgroups. The
statement is independent of the local graph and requires no commutativity
of `A` or `U`.
-/

namespace Subgroup

private theorem inf_le_of_coprime_quotient
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K N U : Subgroup G) [K.Normal]
    (hcop : ¬ p ∣ Nat.card (N ⧸ K.subgroupOf N)) (hU : IsPGroup p U) :
    U ⊓ N ≤ K := by
  let q := QuotientGroup.mk' (K.subgroupOf N)
  let V := U.subgroupOf N
  have hVp : IsPGroup p V := hU.comap_of_injective N.subtype N.subtype_injective
  have hmapbot : V.map q = ⊥ := by
    rcases (hVp.map q).card_eq_or_dvd with hcard | hdvd
    · exact Subgroup.card_eq_one.mp hcard
    · exact False.elim (hcop (hdvd.trans (Subgroup.card_subgroup_dvd_card _)))
  intro g hg
  let gN : N := ⟨g, hg.2⟩
  have hq : q gN = 1 := by
    have hm : q gN ∈ V.map q := Subgroup.mem_map_of_mem q hg.1
    exact Subgroup.mem_bot.mp (hmapbot ▸ hm)
  have hmem : gN ∈ K.subgroupOf N := (QuotientGroup.eq_one_iff gN).mp hq
  exact hmem

/-- Conjugate subgroups in a common `p`-subgroup have equal images modulo
the lower normal subgroup of a coprime normal section. -/
public theorem map_conjugate_eq_of_coprime_quotient
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K N U A : Subgroup G) [K.Normal] [N.Normal] (_hKN : K ≤ N)
    (hcop : ¬ p ∣ Nat.card (N ⧸ K.subgroupOf N)) (hU : IsPGroup p U)
    (hAU : A ≤ U) (x : G) (hx : x ∈ N) (hAxU : A.conjBy x ≤ U) :
    A.map (QuotientGroup.mk' K) = (A.conjBy x).map (QuotientGroup.mk' K) := by
  have hinter : U ⊓ N ≤ K := inf_le_of_coprime_quotient K N U hcop hU
  have heq (a : G) (ha : a ∈ A) :
      QuotientGroup.mk' K (x * a * x⁻¹) = QuotientGroup.mk' K a := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply hinter
    refine ⟨U.div_mem (hAxU (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)) (hAU ha), ?_⟩
    have hn := N.mul_mem hx ((inferInstance : N.Normal).conj_mem x⁻¹ (N.inv_mem hx) a)
    change (x * a * x⁻¹) / a ∈ N
    simpa only [div_eq_mul_inv, mul_assoc] using hn
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨x * a * x⁻¹, ⟨a, ha, rfl⟩, heq a ha⟩
  · rintro _ ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (heq a ha).symm⟩

/-- Compare the original subgroup with its conjugate modulo the lower
normal subgroup of a coprime normal section. -/
public theorem conjugate_subgroup_le_sup_of_coprime_quotient
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K N U A : Subgroup G) [K.Normal] [N.Normal] (hKN : K ≤ N)
    (hcop : ¬ p ∣ Nat.card (N ⧸ K.subgroupOf N)) (hU : IsPGroup p U)
    (hAU : A ≤ U) (x : G) (hx : x ∈ N) (hAxU : A.conjBy x ≤ U) :
    A ≤ A.conjBy x ⊔ K := by
  have hmap := map_conjugate_eq_of_coprime_quotient K N U A hKN hcop hU hAU x hx hAxU
  have hc := congrArg (Subgroup.comap (QuotientGroup.mk' K)) hmap
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hc
  exact le_sup_left.trans hc.le

end Subgroup
