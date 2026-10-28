module

public import Theory.PPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Prime-complement cores in products and quasisimple extensions

A normal subgroup of order prime to p has trivial intersection with a
subgroup whose p'-core is trivial. This gives product and quotient reductions.
In particular, across a q-group quotient the remaining p'-core is a q-group,
so a trivial q-core eliminates it. For a quasisimple group, the only other
normal subgroups are central; a p-group center and p dividing the group order
therefore suffice.

These elementary reductions are used for the group alternatives in
Aschbacher–Smith, *The Classification of Quasithin Groups*, B.5.6, p.105.
They do not assume a classification theorem.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H J : Type*} [Group G] [Group H] [Group J]
variable {p q : ℕ} [Fact p.Prime]

/-- A surjection carries the prime-complement core into the target core. -/
theorem pPrimeCore_map_le [Finite G] (f : G →* H) (hf : Function.Surjective f) :
    (pPrimeCore p G).map f ≤ pPrimeCore p H := by
  apply le_sSup
  exact ⟨Subgroup.Normal.map inferInstance f hf,
    pPrimeCore_coprime_card.of_dvd_right (card_map_dvd _ _)⟩

omit [Fact p.Prime] in
/-- A normal p'-subgroup has trivial intersection with any subgroup having
trivial p'-core. Normality is only required of the first subgroup. -/
theorem normal_coprime_inf_eq_bot [Finite G] (N L : Subgroup G) [N.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (hL : pPrimeCore p L = ⊥) : N ⊓ L = ⊥ := by
  have h : N.subgroupOf L = ⊥ := pPrimeCore_eq_bot_iff.mp hL _ inferInstance
    (hN.of_dvd_right (card_comap_dvd_of_injective N L.subtype L.subtype_injective))
  apply eq_bot_iff.mpr
  intro x hx
  have hx0 : (⟨x, hx.2⟩ : L) ∈ N.subgroupOf L := hx.1
  rw [h, mem_bot] at hx0
  exact mem_bot.mpr (congrArg Subtype.val hx0)

/-- Trivial p'-core is preserved by a direct product. -/
theorem pPrimeCore_prod_eq_bot [Finite G] [Finite H]
    (hG : pPrimeCore p G = ⊥) (hH : pPrimeCore p H = ⊥) :
    pPrimeCore p (G × H) = ⊥ := by
  have h₁ := pPrimeCore_map_le (p := p) (MonoidHom.fst G H) Prod.fst_surjective
  have h₂ := pPrimeCore_map_le (p := p) (MonoidHom.snd G H) Prod.snd_surjective
  rw [hG] at h₁
  rw [hH] at h₂
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  exact Prod.ext
    (mem_bot.mp (h₁ (mem_map_of_mem _ hx)))
    (mem_bot.mp (h₂ (mem_map_of_mem _ hx)))

omit [Fact p.Prime] in
/-- Transport triviality through an actual group isomorphism. -/
theorem pPrimeCore_eq_bot_of_equiv (e : G ≃* H) (hH : pPrimeCore p H = ⊥) :
    pPrimeCore p G = ⊥ := by
  exact (map_eq_bot_iff_of_injective _ e.injective).mp
    ((pPrimeCore_map_iso p e).trans hH)

/-- If the normal subgroup has trivial p'-core, the p'-core injects into
the quotient. Thus a q-group quotient and trivial q-core eliminate it. -/
theorem pPrimeCore_eq_bot_of_pCore_eq_bot_of_quotient [Finite G] [Fact q.Prime]
    (N : Subgroup G) [N.Normal] (hN : pPrimeCore p N = ⊥)
    (hQ : IsPGroup q (G ⧸ N)) (hG : pCore q G = ⊥) :
    pPrimeCore p G = ⊥ := by
  let O := pPrimeCore p G
  have hi : O ⊓ N = ⊥ := normal_coprime_inf_eq_bot O N pPrimeCore_coprime_card hN
  let f : O →* G ⧸ N := (QuotientGroup.mk' N).comp O.subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply eq_bot_iff.mpr
    intro x hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have hx1 : (x : G) = 1 := mem_bot.mp (hi.le ⟨x.property, hxN⟩)
    exact mem_bot.mpr (Subtype.ext hx1)
  have hp : IsPGroup q O := hQ.of_injective f hf
  exact le_bot_iff.mp ((show O ≤ pCore q G from le_sSup ⟨inferInstance, hp⟩).trans hG.le)

/-- A self-centralizing normal subgroup with trivial p'-core forces the
same conclusion in the ambient group. -/
theorem pPrimeCore_eq_bot_of_selfCentralizing [Finite G]
    (L : Subgroup G) [L.Normal] (hL : pPrimeCore p L = ⊥)
    (hC : centralizer (L : Set G) ≤ L) : pPrimeCore p G = ⊥ := by
  have hi : pPrimeCore p G ⊓ L = ⊥ :=
    normal_coprime_inf_eq_bot _ _ pPrimeCore_coprime_card hL
  have hc : ⁅pPrimeCore p G, L⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_le_inf _ _).trans hi.le)
  have hle : pPrimeCore p G ≤ L :=
    (commutator_eq_bot_iff_le_centralizer.mp hc).trans hC
  simpa only [inf_eq_left.mpr hle] using hi

/-- For order dividing pᵃqᵇ, removing p leaves a q-group. This is useful
when the existing q-core hypothesis already rules that subgroup out. -/
theorem pPrimeCore_eq_bot_of_card_dvd [Finite G] [Fact q.Prime]
    (a b : ℕ) (hcard : Nat.card G ∣ p ^ a * q ^ b) (hcore : pCore q G = ⊥) :
    pPrimeCore p G = ⊥ := by
  have hdiv := (pPrimeCore p G).card_subgroup_dvd_card.trans hcard
  have hcop := (pPrimeCore_coprime_card (p := p) (G := G)).symm.pow_right a
  have hq : IsPGroup q (pPrimeCore p G) :=
    IsPGroup.of_card_dvd_pow (hcop.dvd_mul_left.mp hdiv)
  exact le_bot_iff.mp ((show pPrimeCore p G ≤ pCore q G from
    le_sSup ⟨inferInstance, hq⟩).trans hcore.le)

/-- A quasisimple group's p'-core vanishes when its center is a p-group
and its order is divisible by p. -/
theorem IsQuasisimple.pPrimeCore_eq_bot [Finite G] [IsQuasisimple G]
    (hZ : IsPGroup p (center G)) (hp : p ∣ Nat.card G) : pPrimeCore p G = ⊥ := by
  rcases IsQuasisimple.normal_le_center_or_eq_top (pPrimeCore p G) with hc | ht
  · have hi : IsPGroup p (pPrimeCore p G) := hZ.of_injective
      (Subgroup.inclusion hc) (Subgroup.inclusion_injective hc)
    apply eq_bot_iff.mpr
    intro x hx
    have he : (⟨x, hx⟩ : pPrimeCore p G) = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hi.orderOf_coprime pPrimeCore_coprime_card ⟨x, hx⟩)
        dvd_rfl (orderOf_dvd_natCard _))
    exact mem_bot.mpr (congrArg Subtype.val he)
  · have hcop := pPrimeCore_coprime_card (p := p) (G := G)
    rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv] at hcop
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop) hp).elim

omit [Fact p.Prime] in
/-- A simple group whose order is divisible by three has trivial three-prime core. -/
theorem pPrimeCore_eq_bot_of_simple [Finite G] [IsSimpleGroup G]
    (h3 : 3 ∣ Nat.card G) : pPrimeCore 3 G = ⊥ := by
  rcases (inferInstance : (pPrimeCore 3 G).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hc := pPrimeCore_coprime_card (p := 3) (G := G)
    rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
    exact ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mp hc h3).elim

end Theory.GroupTheory
