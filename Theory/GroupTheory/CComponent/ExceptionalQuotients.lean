module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.PPrimeCore
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Comparing exceptional component images in the two core quotients

For a subnormal subgroup L whose intrinsic two-core quotient has trivial
three-prime core, L ∩ O₃′(G) is exactly O₂(L). The first isomorphism theorem
then identifies L/O₂(L) with its image in G/O₃′(G). This compares the
component images, without asserting equality of the ambient cores.

Both A₇ and the concrete even hexacode group have trivial three-prime core.
For the cover this follows from quasisimplicity and its center of order
three. Source application: Aschbacher–Smith, combined manuscript (1 March
2004), A.3.18, printed pp.51–52, used in 15.3.49(k), p.1144.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.CComponentExceptionalQuotient

theorem primeCore_bot {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hz : IsPGroup 3 (center Q)) (hc : 3 ∣ Nat.card Q) : pPrimeCore 3 Q = ⊥ := by
  rcases IsQuasisimple.normal_le_center_or_eq_top (pPrimeCore 3 Q) with hle | ht
  · obtain ⟨n, hn⟩ := hz.exists_card_eq
    have hcop : Nat.Coprime (Nat.card (center Q)) (Nat.card (pPrimeCore 3 Q)) := by
      rw [hn]
      exact pPrimeCore_coprime_card.pow_left n
    have hd := (disjoint_of_coprime_natCard hcop).eq_bot
    rw [inf_eq_right.mpr hle] at hd
    exact hd
  · have hcop := pPrimeCore_coprime_card (p := 3) (G := Q)
    rw [ht, Nat.card_congr (topEquiv : (⊤ : Subgroup Q) ≃* Q).toEquiv] at hcop
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop hc).elim

theorem seven_primeCore_bot : pPrimeCore 3 (alternatingGroup (Fin 7)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hn := (pPrimeCore_normal (p := 3) (G := alternatingGroup (Fin 7))).eq_bot_or_eq_top
  rcases hn with hn | hn
  · exact hn
  · have hcop := pPrimeCore_coprime_card (p := 3) (G := alternatingGroup (Fin 7))
    rw [hn, Nat.card_congr (topEquiv : (⊤ : Subgroup (alternatingGroup (Fin 7))) ≃*
      alternatingGroup (Fin 7)).toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcop
    norm_num [Nat.factorial] at hcop

theorem even_primeCore_bot : pPrimeCore 3 Atlas.Codes.HexEvenAutomorphisms = ⊥ := by
  let _ := Representation.Hexacode.even_isQuasisimple
  exact primeCore_bot (IsPGroup.of_card (n := 1) (by
    simpa using Representation.Hexacode.even_center_card)) (by
      rw [Atlas.Codes.hexEven_card]
      decide)

theorem core_comap {G : Type*} [Group G] [Finite G] (L : Subgroup G)
    (hL : L.IsSubnormal) (hq : pPrimeCore 3 (L ⧸ pCore 2 L) = ⊥) :
    (pPrimeCore 3 G).comap L.subtype = pCore 2 L := by
  let q := QuotientGroup.mk' (pCore 2 L)
  let N := (pPrimeCore 3 G).comap L.subtype
  have hNc : Nat.Coprime 3 (Nat.card N) :=
    pPrimeCore_coprime_card.of_dvd_right
      (card_comap_dvd_of_injective _ _ L.subtype_injective)
  have hm : N.map q ≤ pPrimeCore 3 (L ⧸ pCore 2 L) := by
    apply le_sSup
    exact ⟨(inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _),
      hNc.of_dvd_right (card_map_dvd N q)⟩
  apply le_antisymm
  · intro x hx
    have hmem : q x ∈ N.map q := mem_map_of_mem q hx
    have hzero : q x = 1 := by simpa only [hq, mem_bot] using hm hmem
    exact (QuotientGroup.eq_one_iff x).mp hzero
  · have h23 : pCore 2 G ≤ pPrimeCore 3 G := by
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
      rw [hn]
      exact (show Nat.Coprime 3 2 by decide).pow_right n
    exact map_le_iff_le_comap.mp ((pCoreIn_le_of_subnormal 2 hL).trans h23)

noncomputable def quotientEquiv {G : Type*} [Group G] [Finite G] (L : Subgroup G)
    (hL : L.IsSubnormal) (hq : pPrimeCore 3 (L ⧸ pCore 2 L) = ⊥) :
    (L ⧸ pCore 2 L) ≃* L.map (QuotientGroup.mk' (pPrimeCore 3 G)) := by
  let f := (QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap L
  have hk : f.ker = pCore 2 L := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact core_comap L hL hq
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap_surjective L))

end Theory.GroupTheory.CComponentExceptionalQuotient
