module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.CyclicNormalOddQuotient.CyclicImage
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Basic
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

/-!
# Cyclic outer action excludes the larger-field Borel shadow

The Borel marking makes S ∩ L normal in Y₊S. Work in the actual quotient
I/C_I(L): its two-group kernel lies in S, so the inner Sylow intersection
and its normalizer transport correctly. The component image has trivial
centralizer, hence the quotient above it embeds in its outer automorphism
group. If that group is cyclic, the Sylow image in the rank-two shadow is
cyclic: its inner kernel is normal and a two-group, and therefore is killed
by O₂ ≤ O_{2,Φ}. This contradicts the four-group Sylow subgroup of S₃ × S₃.

For PSp₄(2ⁿ), n > 1, the actual characteristic-two central-quotient
isomorphism and the proved diagram-preserving automorphism classification
supply outer cyclicity. No hypothesis about universal central covers is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the final
proof of 15.3.35, printed p.1139, retaining 15.3.33, 15.3.36 and 15.3.41.
The common result deliberately leaves outer cyclicity explicit for the
G₂ and triality branches; their model coverage belongs to the caller.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection.CyclicOuter

private theorem no_cyclic_shadow_sylow (P : Sylow 2 SymmetricThreeProduct.G)
    (hP : IsCyclic P) : False := by
  have hb : IsCyclic SymmetricThreeProduct.borel :=
    (P.equiv SymmetricThreeProduct.sylow).isCyclic.mp hP
  let := hb
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := SymmetricThreeProduct.borel)
  have hs : ∀ x : SymmetricThreeProduct.borel, x ^ 2 = 1 := by decide +kernel
  have hd := orderOf_dvd_of_pow_eq_one (hs x)
  rw [hx, SymmetricThreeProduct.card_borel] at hd
  norm_num at hd

variable {K : Type*} [Group K] [Finite K]

private theorem no_shadow_of_cyclic_quotient (D Y : Subgroup K) [D.Normal]
    (T : Sylow 2 K) [IsCyclic (K ⧸ D)]
    (hY : Y ≤ normalizer (((T : Subgroup K) ⊓ D : Subgroup K) : Set K))
    (hshadow : RankTwoShadow Y T) : False := by
  let H := Y ⊔ (T : Subgroup K)
  let N := ((T : Subgroup K) ⊓ D).subgroupOf H
  have hTH : (T : Subgroup K) ≤ H := le_sup_right
  have hTN : (T : Subgroup K) ≤ normalizer (((T : Subgroup K) ⊓ D : Subgroup K) : Set K) := by
    exact (le_inf (T : Subgroup K).le_normalizer
      (le_normalizer_of_normal (H := D))).trans inf_normalizer_le_normalizer_inf
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le hY hTN)
  have hp : IsPGroup 2 N := (T.isPGroup'.to_le inf_le_left).comap_subtype
  have hc : N ≤ pCore 2 H := le_sSup ⟨inferInstance, hp⟩
  have hn : N ≤ twoFrattiniCore H := by
    intro x hx
    change QuotientGroup.mk' (pCore 2 H) x ∈ frattini (H ⧸ pCore 2 H)
    have he : QuotientGroup.mk' (pCore 2 H) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr (hc hx)
    rw [he]
    exact one_mem _
  let P := T.subtype hTH
  let q : H →* SymmetricThreeProduct.G :=
    hshadow.some.toMonoidHom.comp (QuotientGroup.mk' (twoFrattiniCore H))
  have hq : Function.Surjective q :=
    hshadow.some.surjective.comp (QuotientGroup.mk'_surjective _)
  let d : P →* K ⧸ D := (QuotientGroup.mk' D).comp (H.subtype.comp (P : Subgroup H).subtype)
  let f : P →* SymmetricThreeProduct.G := q.comp (P : Subgroup H).subtype
  have hker : d.ker ≤ f.ker := by
    intro x hx
    have hxD : ((x : H) : K) ∈ D := (QuotientGroup.eq_one_iff _).mp hx
    have hxN : (x : H) ∈ N := ⟨x.property, hxD⟩
    change hshadow.some (QuotientGroup.mk' (twoFrattiniCore H) (x : H)) = 1
    have he : QuotientGroup.mk' (twoFrattiniCore H) (x : H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hn hxN)
    rw [he, map_one]
  have hf : IsCyclic f.range := isCyclic_range_of_ker_le_cyclic d f hker
  have hcyc : IsCyclic (P.mapSurjective hq) := by
    change IsCyclic ((P : Subgroup H).map q)
    have he : f.range = (P : Subgroup H).map q := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.property, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    exact he ▸ hf
  exact no_cyclic_shadow_sylow _ hcyc


variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The Borel marking supplies normalization of the actual inner Sylow intersection. -/
private theorem borel_normalizes_intersection {L S B Y : Subgroup G}
    (hB : BorelOverSylow L S B) (hYB : Y ≤ B) :
    Y ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨P, hP, rfl⟩ := hB
  exact hYB.trans (hP ▸ (P : Subgroup L).le_normalizer_map L.subtype)

/-- Cyclic outer automorphisms are incompatible with the Borel rank-two shadow. -/
theorem false_of_cyclic_outer
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B)
    (houter : IsCyclic (MulAut.Outer (componentImage I L L))) : False := by
  let q := centralizerQuotientMap (L.subgroupOf I)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let D := componentImage I L L
  let : D.Normal := (inferInstance : (L.subgroupOf I).Normal).map q hq
  let : IsQuasisimple L := c.component_quasisimple
  let : IsQuasisimple (L.subgroupOf I) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe c.component_le).symm
  have hcentral : centralizer (D : Set (ComponentQuotient I L)) = ⊥ :=
    centralizerQuotientComponent_centralizer (L.subgroupOf I)
  let : IsCyclic (MulAut.Outer D) := houter
  let : IsCyclic (ComponentQuotient I L ⧸ D) :=
    isCyclic_of_injective (MulAut.outerAction D) (MulAut.outerAction_injective D hcentral)
  obtain ⟨P, hP⟩ := c.sylow
  have hPS : (P : Subgroup I) = S.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le (hP ▸ map_subtype_le _)]
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hZ : IsPGroup 2 (center L) := c.center_eq ▸ pCore_isPGroup
  have hk : IsPGroup 2 q.ker := component_kernel_isTwoGroup
    c.component_le c.join_eq hS hZ
  have hkS : q.ker ≤ S.subgroupOf I := hPS ▸ hk.le_sylow_of_normal P
  have hi : ((S ⊓ L).subgroupOf I).map q =
      componentImage I L S ⊓ D := by
    change (S.subgroupOf I ⊓ L.subgroupOf I).map q = _
    rw [inf_comm, map_inf_of_ker_le q _ _ hkS, inf_comm]
    rfl
  have hn : Yplus.subgroupOf I ≤
      normalizer (((S ⊓ L).subgroupOf I) : Set I) := by
    rw [← subgroupOf_normalizer_eq (inf_le_right.trans c.component_le)]
    exact comap_mono (borel_normalizes_intersection hB hYB)
  have hnq : componentImage I L Yplus ≤
      normalizer ((componentImage I L S ⊓ D : Subgroup _) : Set _) := by
    rw [← hi]
    exact (map_mono hn).trans (Subgroup.le_normalizer_map _)
  obtain ⟨T, hT⟩ := componentImage_sylow I L S P hP
  apply no_shadow_of_cyclic_quotient D (componentImage I L Yplus) T
  · simpa only [hT, coe_inf] using hnq
  · rw [hT]
    exact componentImage_rankTwoShadow c.component_le c.join_eq hS hZ c.yplus_le c.shadow


open Theory.SpecificGroups.SymplecticFour

/-- The actual PSp₄(2ⁿ) model has cyclic outer automorphism group. -/
theorem outer_isCyclic_of_symplectic_model {A : Type*} [Group A]
    (n : ℕ) (hn : 1 < n) (hmodel : ClassicalGroup.IsPSp A 2 (2^n)) :
    IsCyclic (MulAut.Outer A) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := EvenProjective.charTwo_of_card hcard
  let : IsCyclic (MulAut.Outer (Sp F)) :=
    DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card hcard hn
      DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
  let e' : A ≃* Sp F := e.trans EvenProjective.equiv.symm
  exact isCyclic_of_injective (MulAut.outerCongr e').toMonoidHom
    (MulAut.outerCongr e').injective


/-- The larger-field symplectic branch is incompatible with the source Borel shadow. -/
theorem false_of_symplectic
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B)
    (n : ℕ) (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSp (componentImage I L L) 2 (2 ^ n)) : False :=
  false_of_cyclic_outer I L M Yplus S B c hB hYB
    (outer_isCyclic_of_symplectic_model n hn hmodel)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection.CyclicOuter
