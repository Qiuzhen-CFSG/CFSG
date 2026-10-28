module

public import Theory.GroupTheory.IsolatedFourTwoGroup
public import Theory.GroupTheory.InvolutionElementaryEight
public import Theory.Frattini.PGroupMap

/-!
# No isolated four-groups when involutions lie in elementary eights

If every involution of a finite group belongs to an elementary binary subgroup
of order at least eight, every elementary four-group commutes with a distinct
four-group. In particular this holds in a finite simple group containing an
elementary eight.

The proof is the first half of GLS, volume 4, Chapter 2, Lemma 18.1
(`refs/KGroup/GLS4/Chapter2.tex`). Isolation forces all involutions of a
two-subgroup of the centralizer into the four-group. The rank-three local
structure gives a strictly larger such two-subgroup. Extending it to Sylow
subgroups of the three involution centralizers bounds its Frattini intersection
by each of the three lines. Thus its Frattini subgroup is trivial, contradicting
maximality of the elementary four-group.
-/

namespace Subgroup
open scoped Pointwise IsMulCommutative

private theorem isolated_four_subgroupOf
    {G : Type*} [Group G] [Finite G] (V P : Subgroup G) (hVP : V ≤ P)
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (V : Set G) → W = V) :
    ∀ W : Subgroup P, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (V.subgroupOf P : Set P) → W = V.subgroupOf P := by
  intro W hWe hW hWC
  let : IsElementaryAbelian 2 W := hWe
  have hm : W.map P.subtype = V := hiso _ (IsElementaryAbelian.map P.subtype)
    (by simpa only [card_map_of_injective P.subtype_injective] using hW) (by
      rintro x ⟨w, hw, rfl⟩ v hv
      exact congrArg Subtype.val (hWC hw ⟨v, hVP hv⟩ hv))
  apply map_injective P.subtype_injective
  rw [hm, map_subgroupOf_eq_of_le hVP]

private theorem sylow_contains_elementary_eight
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A) :
    ∃ E : Subgroup S, IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  obtain ⟨Q, hAQ⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  let f := (MulAut.conj g).toMonoidHom
  let B := A.map f
  have hBS : B ≤ (S : Subgroup G) := by
    rintro x ⟨a, ha, rfl⟩
    rw [← hg]
    change (MulAut.conj g) • a ∈ (MulAut.conj g) • (Q : Set G)
    exact Set.smul_mem_smul_set (hAQ ha)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  refine ⟨B.subgroupOf (S : Subgroup G), IsElementaryAbelian.subgroupOf hBS, ?_⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe hBS).toEquiv,
    card_map_of_injective (MulAut.conj g).injective]
  exact hA

private theorem exists_rank_three_overgroup_in_centralizer
    {G : Type*} [Group G] [Finite G]
    (height : ∀ t : G, orderOf t = 2 →
      ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A ∧ t ∈ A)
    (R : Subgroup G) (hR : IsPGroup 2 R) (t : G) (ht : orderOf t = 2)
    (hRC : R ≤ centralizer ({t} : Set G)) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ R ≤ P ∧ P ≤ centralizer ({t} : Set G) ∧
      ∃ E : Subgroup P, IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  let C := centralizer ({t} : Set G)
  have hRC' : IsPGroup 2 (R.subgroupOf C) :=
    hR.of_injective (subgroupOfEquivOfLe hRC).toMonoidHom
      (subgroupOfEquivOfLe hRC).injective
  obtain ⟨S, hRS⟩ := hRC'.exists_le_sylow
  obtain ⟨A, hAe, hA8, htA⟩ := height t ht
  let : IsElementaryAbelian 2 A := hAe
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨t, htA⟩))
  let AC := A.subgroupOf C
  let : IsElementaryAbelian 2 AC := IsElementaryAbelian.subgroupOf hAC
  have hAC8 : 8 ≤ Nat.card AC := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
    exact hA8
  obtain ⟨E, hEe, hE8⟩ := sylow_contains_elementary_eight S AC hAC8
  let P := (S : Subgroup C).map C.subtype
  let e : S ≃* P := (S : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
  let : IsElementaryAbelian 2 E := hEe
  refine ⟨P, S.isPGroup'.map C.subtype, ?_, map_subtype_le _,
    E.map e.toMonoidHom, IsElementaryAbelian.map _, ?_⟩
  · intro r hr
    exact mem_map.mpr ⟨⟨r, hRC hr⟩, hRS hr, rfl⟩
  · simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using hE8

private theorem exists_larger_two_subgroup_centralizing_isolated_four
    {G : Type*} [Group G] [Finite G]
    (height : ∀ t : G, orderOf t = 2 →
      ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A ∧ t ∈ A)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hV : Nat.card V = 4)
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (V : Set G) → W = V) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ V < R ∧ R ≤ centralizer (V : Set G) := by
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t, ht1⟩ := exists_ne (1 : V)
  have hto : orderOf (t : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (t : G) t.property)
    (by simpa using ht1)
  have hVC : V ≤ centralizer ({(t : G)} : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr (V.le_centralizer t.property v hv)
  obtain ⟨P, hP, hVP, hPC, E, hEe, hE8⟩ :=
    exists_rank_three_overgroup_in_centralizer height V
      (IsElementaryAbelian.isPGroup 2 V) t hto hVC
  let VP := V.subgroupOf P
  let : IsElementaryAbelian 2 VP := IsElementaryAbelian.subgroupOf hVP
  let : IsElementaryAbelian 2 E := hEe
  have hVP4 : Nat.card VP = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv).trans hV
  have hlt := lt_centralizer_of_isolated_four_of_rank_three hP E VP hE8 hVP4
    (isolated_four_subgroupOf V P hVP hiso)
  let D := centralizer (VP : Set P)
  let R := D.map P.subtype
  have hVR : V ≤ R := by
    intro v hv
    exact mem_map.mpr ⟨⟨v, hVP hv⟩, VP.le_centralizer hv, rfl⟩
  refine ⟨R, (hP.to_subgroup D).map P.subtype, lt_of_le_not_ge hVR ?_, ?_⟩
  · intro hRV
    apply hlt.not_ge
    intro d hd
    exact hRV (mem_map_of_mem P.subtype hd)
  · rintro r ⟨d, hd, rfl⟩ v hv
    exact congrArg Subtype.val (hd ⟨v, hVP hv⟩ hv)

private theorem inf_frattini_le_each_involution
    {G : Type*} [Group G] [Finite G]
    (height : ∀ t : G, orderOf t = 2 →
      ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A ∧ t ∈ A)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hV : Nat.card V = 4)
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (V : Set G) → W = V)
    (R : Subgroup G) (hR : IsPGroup 2 R) (hVR : V ≤ R)
    (hRC : R ≤ centralizer (V : Set G))
    (t : G) (htV : t ∈ V) (ht : orderOf t = 2) :
    V ⊓ (frattini R).map R.subtype ≤ zpowers t := by
  have hRCt : R ≤ centralizer ({t} : Set G) := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (hRC hr t htV).symm
  obtain ⟨P, hP, hRP, hPC, E, hEe, hE8⟩ :=
    exists_rank_three_overgroup_in_centralizer height R hR t ht hRCt
  have hVP := hVR.trans hRP
  let VP := V.subgroupOf P
  let : IsElementaryAbelian 2 VP := IsElementaryAbelian.subgroupOf hVP
  let : IsElementaryAbelian 2 E := hEe
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let tP : P := ⟨t, hVP htV⟩
  have htZ : tP ∈ center P := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hPC x.property))
  have hbound := inf_frattini_le_zpowers_of_isolated_four_of_rank_three hP E VP hE8
    ((Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv).trans hV)
    (isolated_four_subgroupOf V P hVP hiso) tP htV (by simpa [tP] using ht) htZ
  rintro x ⟨hxV, r, hr, rfl⟩
  have hrP : inclusion hRP r ∈ frattini P :=
    frattini_map_le_of_isPGroup (p := 2) (inclusion hRP)
      (mem_map_of_mem (inclusion hRP) hr)
  have hrline := hbound ⟨hxV, hrP⟩
  have hm := mem_map_of_mem P.subtype hrline
  rw [MonoidHom.map_zpowers] at hm
  exact hm

/-- If every involution belongs to an elementary binary subgroup of order
at least eight, every elementary four-group has a distinct commuting four-group. -/
public theorem exists_distinct_commuting_four_of_involution_eights
    {G : Type*} [Group G] [Finite G]
    (height : ∀ t : G, orderOf t = 2 →
      ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A ∧ t ∈ A)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hV : Nat.card V = 4) :
    ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ Nat.card W = 4 ∧
      W ≤ centralizer (V : Set G) ∧ W ≠ V := by
  classical
  by_contra! hiso
  obtain ⟨R, hR, hVR, hRC⟩ :=
    exists_larger_two_subgroup_centralizing_isolated_four height V hV hiso
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  have hinf : V ⊓ (frattini R).map R.subtype = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    change x = 1
    by_contra hx1
    have hxo : orderOf x = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1) hx1
    have hnot : ¬ V ≤ zpowers x := by
      intro hle
      have hc := card_le_of_le hle
      rw [hV, Nat.card_zpowers, hxo] at hc
      omega
    obtain ⟨t, htV, htout⟩ := SetLike.not_le_iff_exists.mp hnot
    have hto : orderOf t = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) t htV)
      (fun ht1 => htout (ht1 ▸ (zpowers x).one_mem))
    have hxline := inf_frattini_le_each_involution height V hV hiso R hR hVR.le hRC t htV hto hx
    have heq : zpowers x = zpowers t := eq_of_le_of_card_ge (zpowers_le.mpr hxline)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hto])
    exact htout (heq ▸ mem_zpowers t)
  have hphi : frattini R = ⊥ := by
    by_contra hne
    let : Nontrivial (frattini R) := (Subgroup.nontrivial_iff_ne_bot (frattini R)).mpr hne
    have hF := hR.to_subgroup (frattini R)
    obtain ⟨n, hn, hc⟩ := hF.nontrivial_iff_card.mp inferInstance
    have hdvd : 2 ∣ Nat.card (frattini R) := by
      rw [hc]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨x, hxo⟩ := exists_prime_orderOf_dvd_card' (G := frattini R) 2 hdvd
    have hxG : orderOf ((x : R) : G) = 2 := by simpa using hxo
    have hxV : ((x : R) : G) ∈ V := involution_mem_of_maximal_elementary_four V
      (maximal_elementary_of_isolated_four V hV hiso) _
      (by simpa [hxG] using pow_orderOf_eq_one ((x : R) : G)) (hRC (x : R).property)
    have hxbot : ((x : R) : G) ∈ (⊥ : Subgroup G) := hinf ▸
      (show ((x : R) : G) ∈ V ⊓ (frattini R).map R.subtype from
        ⟨hxV, mem_map_of_mem R.subtype x.property⟩)
    have hxone : ((x : R) : G) = 1 := hxbot
    simp [hxone] at hxG
  let : IsElementaryAbelian 2 R := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  exact hVR.not_ge (maximal_elementary_of_isolated_four V hV hiso R inferInstance hVR.le)

/-- In a finite simple group containing an elementary eight, the ambient
commuting graph of elementary four-groups has no isolated vertices. -/
public theorem exists_distinct_commuting_four_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hV : Nat.card V = 4) :
    ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ Nat.card W = 4 ∧
      W ≤ centralizer (V : Set G) ∧ W ≠ V :=
  exists_distinct_commuting_four_of_involution_eights
    (Sylow.exists_elementary_eight_of_simple E hE) V hV

end Subgroup
