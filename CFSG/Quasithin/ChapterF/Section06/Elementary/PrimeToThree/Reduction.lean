module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.Quotient

/-!
# Removing the two-core in the collapsed-image case

The prime-to-three core commutes with quotienting by the two-core, because
that kernel has order prime to three. The restricted quotient map therefore
identifies `O₃′(G)/O₂(G)` with the actual prime-to-three core of `G/O₂(G)`.
The supplement identities also pass to this quotient. When the ambient
two-core is trivial, a local supplement is genuinely isomorphic to S₃.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.11(2), the reduction on printed p.307.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem primeToThreeCore_map_quotientTwoCore :
    (pPrimeCore 3 G).map (QuotientGroup.mk' (pCore 2 G)) =
      pPrimeCore 3 (G ⧸ pCore 2 G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have he := pPrimeCore_comap_eq_of_surjective_coprime 3 q
    (QuotientGroup.mk'_surjective _) hk
  rw [← he, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

noncomputable def primeToThreeCoreQuotientTwoCoreEquiv :
    ((pPrimeCore 3 G) ⧸ (pCore 2 G).subgroupOf (pPrimeCore 3 G)) ≃*
      pPrimeCore 3 (G ⧸ pCore 2 G) :=
  ((QuotientGroup.quotientMulEquivOfEq (by rw [QuotientGroup.ker_mk'])).trans
    (RankTwoAmalgam.subgroupQuotientMapEquiv (QuotientGroup.mk' (pCore 2 G))
      (pPrimeCore 3 G))).trans
    (MulEquiv.subgroupCongr primeToThreeCore_map_quotientTwoCore)

theorem primeToThreeCoreQuotientTwoCoreEquiv_mk (x : pPrimeCore 3 G) :
    ((primeToThreeCoreQuotientTwoCoreEquiv (G := G)) (QuotientGroup.mk' _ x) :
      G ⧸ pCore 2 G) = QuotientGroup.mk' (pCore 2 G) x.val := by rfl

theorem IsGoldschmidtTriple.left_equiv_symmetricThree_of_supplement
    (h : IsGoldschmidtTriple G₁ G₂) (hQ : pCore 2 G = ⊥)
    (hgen : G₁ ⊔ pPrimeCore 3 G = ⊤) : Nonempty (G₁ ≃* Equiv.Perm (Fin 3)) := by
  have he : pCore 2 G₁ = ⊥ := by
    apply Subgroup.map_injective G₁.subtype_injective
    rw [h.primeToThreeCore_supplement_left_core hgen, hQ, Subgroup.map_bot]
  exact ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq he.symm).trans h.quotient_left.some)⟩

theorem IsGoldschmidtTriple.primeToThreeCore_supplement_mod_twoCore
    (_h : IsGoldschmidtTriple G₁ G₂)
    (hgen : G₁ ⊔ pPrimeCore 3 G = ⊤) :
    G₁.map (QuotientGroup.mk' (pCore 2 G)) ⊔
      pPrimeCore 3 (G ⧸ pCore 2 G) = ⊤ := by
  rw [← primeToThreeCore_map_quotientTwoCore, ← Subgroup.map_sup, hgen,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

end CFSG.Quasithin.ChapterF
