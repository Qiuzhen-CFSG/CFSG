module
public import Theory.PPrimeCore

/-!
# The odd-core quotient formulation of Z-star

An element is central modulo a normal subgroup precisely when its commutators
belong to that subgroup. For the odd core this packages quotient centrality
as the normal odd-order subgroup conclusion of Glauberman's Z-star theorem.

The proof applies the quotient equality criterion to gt and tg, then uses
the proved coprime cardinality of the odd core. This ports the elementary
`OddCore` bridge from `public/lean-eval/glauberman_zStar`, keeping the existing
`pPrimeCore` definition. The substantive Z-star theorem must still establish
the quotient-centrality hypothesis.
-/

namespace Glauberman.ZStar

/-- Quotient centrality is equivalent to containment of all commutators. -/
public theorem mem_center_quotient_iff_commutators_mem
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {t : G} :
    QuotientGroup.mk' N t ∈ Subgroup.center (G ⧸ N) ↔
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro ht g
    have h := ht (QuotientGroup.mk' N g)
    have heq : QuotientGroup.mk' N (g * t) = QuotientGroup.mk' N (t * g) := by
      simpa only [map_mul] using h
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc] using
      (QuotientGroup.eq_iff_div_mem.mp heq)
  · intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    have heq : QuotientGroup.mk' N (g * t) = QuotientGroup.mk' N (t * g) :=
      QuotientGroup.eq_iff_div_mem.mpr (by
        simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc] using h g)
    simpa only [map_mul] using heq

/-- Centrality modulo a normal subgroup puts every commutator in it. -/
public theorem commutators_mem_of_mem_center_quotient
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {t : G}
    (ht : QuotientGroup.mk' N t ∈ Subgroup.center (G ⧸ N)) :
    ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N :=
  mem_center_quotient_iff_commutators_mem.mp ht

/-- Commutator containment implies centrality modulo the normal subgroup. -/
public theorem mem_center_quotient_of_commutators_mem
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {t : G}
    (hcomm : ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N) :
    QuotientGroup.mk' N t ∈ Subgroup.center (G ⧸ N) :=
  mem_center_quotient_iff_commutators_mem.mpr hcomm

/-- Package quotient centrality as the normal odd-order subgroup conclusion. -/
public theorem conclusion_of_mem_center_oddCore
    {G : Type*} [Group G] [Finite G] {t : G}
    (ht : QuotientGroup.mk' (pPrimeCore 2 G) t ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G)) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  refine ⟨pPrimeCore 2 G, inferInstance, ?_, mem_center_quotient_iff_commutators_mem.mp ht⟩
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))

/-- A normal subgroup of a core-free group has trivial odd core. -/
public theorem pPrimeCore_subgroup_eq_bot_of_normal
    {G : Type*} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥) (N : Subgroup G) (hN : N.Normal) :
    pPrimeCore 2 N = ⊥ := by
  let : N.Normal := hN
  have hmapbot : (pPrimeCore 2 N).map N.subtype = ⊥ := by
    apply le_bot_iff.mp
    simpa [hcore] using
      pPrimeCore_map_subtype_le_pPrimeCore_of_normal
        (G := G) (p := 2) N
  exact (Subgroup.map_eq_bot_iff_of_injective
    (H := pPrimeCore 2 N) (f := N.subtype) N.subtype_injective).mp hmapbot

end Glauberman.ZStar
