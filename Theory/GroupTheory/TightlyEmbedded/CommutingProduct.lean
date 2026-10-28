module

public import Theory.GroupTheory.TightlyEmbedded
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Tightly embedded simple subgroups in commuting products

A centerless quasisimple tightly embedded subgroup of a direct product lies
in one factor. Otherwise its intersections with both normal factors are
trivial. Write an involution as a product of its two coordinates. Each
coordinate centralizes that involution, hence normalizes the tightly embedded
subgroup. Commutators lie in the trivial intersections, so both coordinates
centralize the subgroup. Their product would be a central involution,
contradicting the trivial center.

This elementary product argument supplies the final containment step in
Aschbacher–Smith, Lemma 16.2.12, printed p.1176, after the earlier residual
identity has put the conjugate component inside the commuting product.
The equivalence transport lemma retains the ambient definition of tight
embedding, including even order and odd intersections.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem normalizer_centralizes_of_disjoint {A K : Subgroup G}
    (hn : K ≤ normalizer (A : Set G)) (hd : Disjoint A K) :
    A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G) := by
  intro a ha k hk
  have hAK : a * k * a⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((mem_normalizer_iff.mp ha.2 k).mp hk) (K.inv_mem hk)
  have hAA : a * k * a⁻¹ * k⁻¹ ∈ A := by
    have hh := A.mul_mem ha.1 ((mem_normalizer_iff.mp (hn hk) a⁻¹).mp (A.inv_mem ha.1))
    simpa only [mul_assoc] using hh
  have he : a * k * a⁻¹ * k⁻¹ = 1 := hd.le_bot ⟨hAA, hAK⟩
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm

/-- A centerless quasisimple tightly embedded subgroup in a commuting direct
product lies in one factor. No order comparison or model list is needed. -/
theorem IsTightlyEmbedded.le_factor_of_commuting_product [Finite G]
    {A B K : Subgroup G} [IsQuasisimple K]
    (ht : IsTightlyEmbedded K) (hc : center K = ⊥)
    (hAB : A ≤ centralizer (B : Set G)) (hd : Disjoint A B)
    (hK : K ≤ A ⊔ B) : K ≤ A ∨ K ≤ B := by
  have hBA : B ≤ centralizer (A : Set G) := le_centralizer_iff.mpr hAB
  have hNA : K ≤ normalizer (A : Set G) :=
    hK.trans (sup_le A.le_normalizer (hBA.trans (centralizer_le_normalizer _)))
  have hNB : K ≤ normalizer (B : Set G) :=
    hK.trans (sup_le (hAB.trans (centralizer_le_normalizer _)) B.le_normalizer)
  let : (A.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hNA
  let : (B.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hNB
  rcases IsQuasisimple.normal_le_center_or_eq_top (A.subgroupOf K) with hAc | hAt
  swap
  · exact Or.inl fun x hx => show (⟨x, hx⟩ : K) ∈ A.subgroupOf K from hAt ▸ mem_top _
  rcases IsQuasisimple.normal_le_center_or_eq_top (B.subgroupOf K) with hBc | hBt
  swap
  · exact Or.inr fun x hx => show (⟨x, hx⟩ : K) ∈ B.subgroupOf K from hBt ▸ mem_top _
  have hAK : Disjoint A K := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hh : (⟨x, hx.2⟩ : K) = 1 := mem_bot.mp (hc ▸ hAc hx.1)
    exact congrArg K.subtype hh
  have hBK : Disjoint B K := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hh : (⟨x, hx.2⟩ : K) = 1 := mem_bot.mp (hc ▸ hBc hx.1)
    exact congrArg K.subtype hh
  obtain ⟨t, ht2⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.mp ht.1)
  have htG : orderOf (t : G) = 2 := (orderOf_injective K.subtype K.subtype_injective t).trans ht2
  have htp : IsPGroup 2 (zpowers (t : G)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, htG]; rfl)
  have htne : zpowers (t : G) ≠ ⊥ := by
    intro he
    have ht1 : (t : G) = 1 := mem_bot.mp (he ▸ mem_zpowers (t : G))
    simp [ht1] at htG
  have hCN : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G) := by
    apply le_trans _ (ht.normalizer_le htp htne (zpowers_le.mpr t.property))
    rw [zpowers_eq_closure, ← centralizer_closure]
    exact centralizer_le_normalizer _
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hAB
  let ab := e.symm ⟨t, hK t.property⟩
  have hab : (ab.1 : G) * (ab.2 : G) = t := by
    rw [← he]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨t, hK t.property⟩)
  have habcomm : Commute (ab.1 : G) (ab.2 : G) := (hAB ab.1.property ab.2 ab.2.property).symm
  have haC : (ab.1 : G) ∈ centralizer ({(t : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hab]
    exact (Commute.refl (ab.1 : G)).mul_right habcomm |>.eq
  have hbC : (ab.2 : G) ∈ centralizer ({(t : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hab]
    exact habcomm.symm.mul_right (Commute.refl (ab.2 : G)) |>.eq
  have haK := normalizer_centralizes_of_disjoint hNA hAK ⟨ab.1.property, hCN haC⟩
  have hbK := normalizer_centralizes_of_disjoint hNB hBK ⟨ab.2.property, hCN hbC⟩
  have htC : (t : G) ∈ centralizer (K : Set G) := hab ▸ (centralizer (K : Set G)).mul_mem haK hbK
  have htZ : t ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (htC k k.property)
  have ht1 : t = 1 := mem_bot.mp (hc ▸ htZ)
  simp [ht1] at ht2

/-- Tight embedding transports through an isomorphism of ambient groups. -/
theorem IsTightlyEmbedded.map_equiv [Finite G] {G' : Type*} [Group G'] [Finite G']
    {K : Subgroup G} (hK : IsTightlyEmbedded K) (e : G ≃* G') :
    IsTightlyEmbedded (K.map e.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using hK.1
  · intro g hg
    have hn : e.symm g ∉ normalizer (K : Set G) := by
      intro hn
      apply hg
      rw [← map_equiv_normalizer_eq K e]
      exact ⟨e.symm g, hn, e.apply_symm_apply g⟩
    have heq : (K.map e.toMonoidHom) ⊓
        (K.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (K ⊓ K.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
      rw [map_inf _ _ e.toMonoidHom e.injective]
      congr 1
      ext x
      simp only [mem_map_equiv, MulAut.conj_symm_apply, map_mul, map_inv]
    rw [heq, card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hK.2 _ hn

end Theory.GroupTheory
