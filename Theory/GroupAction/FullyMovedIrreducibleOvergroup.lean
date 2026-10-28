module
public import Theory.GroupAction.FullyMovedIrreducibleCore
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Restricting a fully moved section to a Sylow overgroup

A subgroup containing a full Sylow and the original actor retains the exact
fixed-point interval, relative two-core and commutator of its elementary
section. Restriction therefore bounds that section by the center of the
self-centralizing two-core of the overgroup.

The J₄ involution-centralizer comparison uses this in Aschbacher--Smith
10.2.9, printed pp.750--751; no fixed vectors are removed.
-/

public section
open Subgroup
namespace Theory.GroupAction
variable {G : Type*} [Group G] [Finite G]
theorem fully_moved_irreducible_card_le_overgroup_core_center (S : Sylow 2 G) (B E K : Subgroup G)
    (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) 
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup G, E ⊓ centralizer (B : Set G) ≤ N → N ≤ E →
      B ≤ normalizer (N : Set G) → N = E ⊓ centralizer (B : Set G) ∨ N = E)
    (hBK : B ≤ K) (hSK : (S : Subgroup G) ≤ K)
    (hC : centralizer (pCore 2 K : Set K) ≤ pCore 2 K) :
    Nat.card E ≤ Nat.card (center (pCore 2 K)) := by
  have hEK := hEB.trans hBK
  have hfix : ((E.subgroupOf K) ⊓ centralizer (B.subgroupOf K : Set K)).map K.subtype =
      E ⊓ centralizer (B : Set G) := by
    apply le_antisymm
    · rintro x ⟨y,⟨hy,hc⟩,rfl⟩
      refine ⟨hy,?_⟩
      intro b hb
      exact congrArg Subtype.val (hc ⟨b,hBK hb⟩ hb)
    · rintro x ⟨hx,hc⟩
      refine ⟨⟨x,hEK hx⟩,⟨hx,?_⟩,rfl⟩
      intro b hb
      exact Subtype.ext (hc b hb)
  have hirr' (N : Subgroup K)
      (hlo : E.subgroupOf K ⊓ centralizer (B.subgroupOf K : Set K) ≤ N)
      (hhi : N ≤ E.subgroupOf K)
      (hn : B.subgroupOf K ≤ normalizer (N : Set K)) :
      N = E.subgroupOf K ⊓ centralizer (B.subgroupOf K : Set K) ∨ N = E.subgroupOf K := by
    have hlo' := map_mono (f := K.subtype) hlo
    rw [hfix] at hlo'
    have hhi' := map_mono (f := K.subtype) hhi
    rw [map_subgroupOf_eq_of_le hEK] at hhi'
    have hn' := (map_mono (f := K.subtype) hn).trans (N.le_normalizer_map K.subtype)
    rw [map_subgroupOf_eq_of_le hBK] at hn'
    rcases hirr (N.map K.subtype) hlo' hhi' hn' with h | h
    · left
      apply map_injective K.subtype_injective
      rwa [hfix]
    · right
      apply map_injective K.subtype_injective
      rwa [map_subgroupOf_eq_of_le hEK]
  let := hE
  have hB' : IsPPerfect 2 (B.subgroupOf K) := hB.of_surjective
    (subgroupOfEquivOfLe hBK).symm.toMonoidHom
    (subgroupOfEquivOfLe hBK).symm.surjective
  have hh := fully_moved_irreducible_card_le_core_center
    (S.subtype hSK) (B.subgroupOf K) (E.subgroupOf K) hB' (by
      intro s hs
      apply mem_normalizer_iff.mpr
      intro b
      exact mem_normalizer_iff.mp (hSB hs) (b : G)) (by
      intro s hs
      apply mem_normalizer_iff.mpr
      intro e
      exact mem_normalizer_iff.mp (hSE hs) (e : G))
    (IsElementaryAbelian.subgroupOf hEK) (comap_mono hEB) (by
      rw [pCoreIn_subgroupOf 2 B K hBK]
      intro b hb e he
      exact Subtype.ext (hcore hb e he)) (by
      apply map_injective K.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hEK,map_subgroupOf_eq_of_le hBK,hmove])
    hirr' hC
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv] at hh

end Theory.GroupAction
