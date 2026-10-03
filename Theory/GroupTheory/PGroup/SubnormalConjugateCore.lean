module
public import Theory.GroupTheory.PGroup.SubnormalQuotientCore
public import Theory.GroupAction.SubgroupConjugation


/-!
# Comparing subnormal conjugators modulo the q-core

Let `p` and `q` be distinct primes, and let `K` be subnormal in a finite
group `G`, with `K/O_q(K)` a `p`-group. If `x ∈ K` and both `A` and
its conjugate by `x` lie in a common `q`-subgroup, then
`A ≤ A.conjBy x ⊔ O_q(G)`.

In the quotient by `O_q(G)`, the subnormal quotient-core theorem puts the
image of `K` in the normal `p`-core. That core meets the image of the common
`q`-subgroup trivially. For every `a ∈ A`, the quotient of its conjugate
by `a` lies in both groups, so the original element and its conjugate have
the same image. Taking the inverse image of the conjugate subgroup's image
gives the containment.

This is the concrete normal-coprime comparison needed for the `R₁` branch
of Stellmacher (9.3), Journal of Algebra 190 (1997), p.49, inside its actual
centralizer group. The ambient companion performs the same comparison
inside a supplied subgroup `C`, retaining the quotient of the original `K`
and returning the ambient image of `O_q(C)`. It transports that quotient
through the canonical subgroup equivalence and maps the intrinsic result
back through `C.subtype`. Both statements require only subnormality of `K`,
not normality or commutativity of the supplied subgroups.
-/

/-- A subnormal conjugator with a coprime-prime quotient identifies the
two supplied q-subgroups modulo the ambient q-core. -/
public theorem subnormal_conjugate_le_sup_pCore
    {G : Type*} [Group G] [Finite G]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (K : Subgroup G) (hK : K.IsSubnormal)
    (hquot : IsPGroup p (K ⧸ pCore q K))
    (U A : Subgroup G) (hU : IsPGroup q U) (hAU : A ≤ U)
    (x : G) (hx : x ∈ K) (hAxU : A.conjBy x ≤ U) :
    A ≤ A.conjBy x ⊔ pCore q G := by
  let π := QuotientGroup.mk' (pCore q G)
  let N := pCore p (G ⧸ pCore q G)
  have hxN : π x ∈ N :=
    subnormal_map_quotient_core_le_pCore p q K hK hquot
      (Subgroup.mem_map_of_mem π hx)
  have hdis : (U.map π) ⊓ N = ⊥ :=
    (IsPGroup.disjoint_of_ne q p (Ne.symm hpq) (U.map π) N (hU.map π)
      (pCore_isPGroup (p := p) (G := G ⧸ pCore q G))).eq_bot
  intro a ha
  let b := x * a * x⁻¹
  have hb : b ∈ A.conjBy x := ⟨a, ha, rfl⟩
  have hdeltaU : π b / π a ∈ U.map π :=
    (U.map π).div_mem (Subgroup.mem_map_of_mem π (hAxU hb))
      (Subgroup.mem_map_of_mem π (hAU ha))
  have hdeltaN : π b / π a ∈ N := by
    have hn := N.mul_mem hxN
      ((inferInstance : N.Normal).conj_mem (π x)⁻¹ (N.inv_mem hxN) (π a))
    simpa [b, map_mul, map_inv, div_eq_mul_inv, mul_assoc] using hn
  have heq : π b = π a := by
    apply div_eq_one.mp
    exact Subgroup.mem_bot.mp (hdis ▸ (show π b / π a ∈ U.map π ⊓ N from ⟨hdeltaU, hdeltaN⟩))
  have hm : a ∈ ((A.conjBy x).map π).comap π := ⟨b, hb, heq⟩
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using hm

/-- The ambient form of the subnormal conjugator comparison inside a supplied
subgroup, retaining the original subgroup's intrinsic quotient hypothesis. -/
public theorem subnormal_conjugate_le_sup_pCore_in
    {G : Type*} [Group G] [Finite G]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (C K : Subgroup G) (hKC : K ≤ C) (hsub : (K.subgroupOf C).IsSubnormal)
    (hquot : IsPGroup p (K ⧸ pCore q K))
    (U A : Subgroup G) (hUC : U ≤ C) (hU : IsPGroup q U) (hAU : A ≤ U)
    (x : G) (hx : x ∈ K) (hAxU : A.conjBy x ≤ U) :
    A ≤ A.conjBy x ⊔ (pCore q C).map C.subtype := by
  let e : K.subgroupOf C ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  let eQ : (K.subgroupOf C ⧸ pCore q (K.subgroupOf C)) ≃* (K ⧸ pCore q K) :=
    QuotientGroup.congr _ _ e (pCore_map_iso q e)
  have hquotC : IsPGroup p (K.subgroupOf C ⧸ pCore q (K.subgroupOf C)) :=
    hquot.of_equiv eQ.symm
  let xC : C := ⟨x, hKC hx⟩
  have hAxC : (A.subgroupOf C).conjBy xC ≤ U.subgroupOf C := by
    rintro _ ⟨a, ha, rfl⟩
    exact hAxU (Subgroup.mem_map.mpr ⟨(a : G), ha, rfl⟩)
  have hlocal := subnormal_conjugate_le_sup_pCore p q hpq (K.subgroupOf C) hsub
    hquotC (U.subgroupOf C) (A.subgroupOf C)
    (hU.comap_of_injective C.subtype C.subtype_injective)
    (Subgroup.subgroupOf_mono C hAU) xC hx hAxC
  have hmap := Subgroup.map_mono (f := C.subtype) hlocal
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (hAU.trans hUC)] at hmap
  have hconj : ((A.subgroupOf C).conjBy xC).map C.subtype = A.conjBy x := by
    unfold Subgroup.conjBy
    rw [Subgroup.map_map]
    have hcomp : C.subtype.comp (MulAut.conj xC).toMonoidHom =
        (MulAut.conj x).toMonoidHom.comp C.subtype := by
      ext a
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (hAU.trans hUC)]
  rwa [hconj] at hmap
