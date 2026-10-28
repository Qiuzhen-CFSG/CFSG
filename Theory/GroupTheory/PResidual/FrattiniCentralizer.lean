module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Frattini

/-!
# Residual centralizers through irreducible Frattini sections

Suppose the image of O²(G) in G/O₂(G) is F. If every ambient normal
subgroup of F has either zero or full image on F/Φ(F), apply this to the
image of C = O²(G) ∩ C_G(O₂(G)). In the full-image case, Frattini
nongeneration gives O²(G) ≤ C O₂(G). The two-perfectness of O²(G)
removes the two-group factor, giving O²(G) ≤ C.

This is the final, purely group-theoretic implication in the odd-prime
branch of Aschbacher–Smith E.5.2, printed p.243. The irreducibility
hypothesis is explicit; establishing it from minimal E-members is a
separate source argument.
-/

namespace Subgroup

private theorem pPerfect_le_normal_of_le_sup_pGroup
    {G : Type*} [Group G] {p : ℕ} (H N R : Subgroup G) [N.Normal]
    (hH : IsPPerfect p H) (hR : IsPGroup p R) (h : H ≤ N ⊔ R) : H ≤ N := by
  let q := QuotientGroup.mk' N
  have hi : H.map q ≤ R.map q := by
    have hm := map_mono (f := q) h
    simpa only [Subgroup.map_sup, q, QuotientGroup.map_mk'_self, bot_sup_eq] using hm
  have hperfect : IsPPerfect p (H.map q) := hH.of_surjective
    (q.subgroupMap H) (q.subgroupMap_surjective H)
  have hpg : IsPGroup p (H.map q) := (hR.map q).to_le hi
  have hb : (⊥ : Subgroup (H.map q)) = ⊤ := hperfect ⊥ inferInstance
    (hpg.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥))
  have hz : H.map q = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hm : (⟨x, hx⟩ : H.map q) ∈ (⊥ : Subgroup (H.map q)) := by rw [hb]; trivial
    exact congrArg Subtype.val (mem_bot.mp hm)
  simpa only [q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz

private theorem eq_of_sup_frattini_eq {G : Type*} [Group G] [Finite G]
    (F C : Subgroup G) (hCF : C ≤ F)
    (h : C ⊔ (frattini F).map F.subtype = F) : C = F := by
  have htop : C.subgroupOf F ⊔ frattini F = ⊤ := by
    apply map_injective F.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hCF, h]
    rw [← MonoidHom.range_eq_map, F.range_subtype]
  have ht := frattini_nongenerating htop
  have hm := congrArg (map F.subtype) ht
  rwa [map_subgroupOf_eq_of_le hCF, ← MonoidHom.range_eq_map, F.range_subtype] at hm

/-- Irreducibility on the actual Frattini section gives the residual-centralizer dichotomy. -/
public theorem pResidual_centralizer_dichotomy_of_frattini_section {G : Type*} [Group G] [Finite G]
    (F : Subgroup (G ⧸ pCore 2 G))
    (hF : (pResidual 2 G).map (QuotientGroup.mk' (pCore 2 G)) = F)
    (hirr : ∀ N : Subgroup (G ⧸ pCore 2 G), N.Normal → N ≤ F →
      N ≤ (frattini F).map F.subtype ∨ N ⊔ (frattini F).map F.subtype = F) :
    pResidual 2 G ≤ centralizer (pCore 2 G : Set G) ∨
      pResidual 2 G ⊓ centralizer (pCore 2 G : Set G) ≤
        ((frattini F).map F.subtype).comap (QuotientGroup.mk' (pCore 2 G)) := by
  let H := pResidual 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let C := H ⊓ centralizer (pCore 2 G : Set G)
  have hCF : C.map q ≤ F := (map_mono inf_le_left).trans hF.le
  let _ : (C.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  rcases hirr (C.map q) inferInstance hCF with hsmall | hfull
  · exact Or.inr (map_le_iff_le_comap.mp hsmall)
  · left
    have heq : C.map q = F := eq_of_sup_frattini_eq F (C.map q) hCF hfull
    have hHC : H.map q ≤ C.map q := by rw [heq]; exact hF.le
    have hHCR : H ≤ C ⊔ pCore 2 G := by
      have hm := (le_comap_map q H).trans (comap_mono hHC)
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', sup_comm] using hm
    exact (pPerfect_le_normal_of_le_sup_pGroup H C (pCore 2 G)
      (isPPerfect_pResidual 2) pCore_isPGroup hHCR).trans inf_le_right

end Subgroup
