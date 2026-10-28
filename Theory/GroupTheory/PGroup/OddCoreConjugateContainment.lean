module
public import Theory.PPrimeCore
public import Theory.GroupAction.SubgroupConjugation

/-!
# Comparing conjugate p-subgroups modulo the p-core

Suppose A and its conjugate by x lie in a common p-subgroup U of a finite
group. If x maps into the p′-core of the quotient by O_p(G), then A lies
in the product of its conjugate and O_p(G). For each a in A, the quotient
of its conjugate by a maps both into the p-group image of U and into the
normal p′-core. Their coprime orders make this element trivial. Thus a and
its conjugate have the same image modulo O_p(G).

The ambient companion carries out this argument inside a specified subgroup
C and maps back through C.subtype, retaining the exact quotient of C.
These elementary comparison lemmas support the first C₀ alternative in
Stellmacher (9.3), Journal of Algebra 190 (1997), p.50, without assuming
subnormality or a single odd-prime-power quotient for the conjugator.
-/

/-- A conjugator in the prime-complement core modulo the p-core identifies
its two conjugate p-subgroups modulo that p-core. -/
public theorem conjugate_le_sup_pCore_of_mem_pPrimeCore_image
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (U A : Subgroup G) (hU : IsPGroup p U) (hAU : A ≤ U)
    (x : G) (hx : (QuotientGroup.mk' (pCore p G)) x ∈
      pPrimeCore p (G ⧸ pCore p G)) (hAxU : A.conjBy x ≤ U) :
    A ≤ A.conjBy x ⊔ pCore p G := by
  let π := QuotientGroup.mk' (pCore p G)
  let N := pPrimeCore p (G ⧸ pCore p G)
  have hxN : π x ∈ N := hx
  have hdis : U.map π ⊓ N = ⊥ := by
    apply Disjoint.eq_bot
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (hU.map π).exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := p) (G := G ⧸ pCore p G)).pow_left n
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

/-- The ambient version inside a supplied subgroup C, using its exact
quotient by its own p-core. -/
public theorem conjugate_le_sup_pCore_of_mem_pPrimeCore_image_in
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (C U A : Subgroup G) (hUC : U ≤ C) (hU : IsPGroup p U) (hAU : A ≤ U)
    (x : G) (hxC : x ∈ C)
    (hx : (QuotientGroup.mk' (pCore p C)) ⟨x, hxC⟩ ∈
      pPrimeCore p (C ⧸ pCore p C)) (hAxU : A.conjBy x ≤ U) :
    A ≤ A.conjBy x ⊔ (pCore p C).map C.subtype := by
  let xC : C := ⟨x, hxC⟩
  have hAxC : (A.subgroupOf C).conjBy xC ≤ U.subgroupOf C := by
    rintro _ ⟨a, ha, rfl⟩
    exact hAxU (Subgroup.mem_map.mpr ⟨(a : G), ha, rfl⟩)
  have hlocal := conjugate_le_sup_pCore_of_mem_pPrimeCore_image p
    (U.subgroupOf C) (A.subgroupOf C)
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
