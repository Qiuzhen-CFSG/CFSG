module
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.RankTwoDisjointAction
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.PPrimeCore

/-!
# Component selection by an external odd prime actor

Let S be perfect with simple quotient by its two-core, inside a normal
subgroup C. An odd prime element outside C and a commuting prime element
of S span an elementary plane. A component of C whose order is divisible
by that prime must contain S: otherwise its normal intersection with S
lies in O₂(S), so the plane is disjoint from it and forces prime rank three.
The same argument for every conjugate gives normality of the component.

The actor need only fix the selected prime element, not the whole of S.
In particular the two-core of S and the actor's action on it are retained.
The component orbit bound is explicit. The original nonblock root-normalizer
application supplies it from the SQTK component theorem.
Source: Aschbacher--Smith, 1.2.1--2 and 4.3.12(1), pp.504--505,617;
the rank obstruction is A.1.27, p.26. This extends the component-selection
argument in OrdinaryRootSecondary/Selection to simple two-core quotients.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.GroupTheory.ExternalPrimeSelection
variable {X : Type*} [Group X] [Finite X]
private theorem prime_component_in_layer {p : ℕ} [Fact p.Prime]
    (hdiv : p ∣ Nat.card (cComponentLayer X)) :
    ∃ K : Subgroup X, K.IsCComponent ∧ p ∣ Nat.card K := by
  classical
  by_contra! h
  let E := cComponentLayer X
  have hE : (⊤ : Subgroup E) ≤ pPrimeCore p E := by
    have hm : E ≤ (pPrimeCore p E).map E.subtype := by
      apply sSup_le
      intro K hK
      have hKE : K ≤ E := le_cComponentLayer hK
      have hn : (K.subgroupOf E).Normal :=
        normal_subgroupOf_of_le_normalizer (cComponentLayer_le_normalizer hK)
      have hc : Nat.Coprime p (Nat.card (K.subgroupOf E)) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hKE).toEquiv]
        exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (h K hK)
      have hp : K.subgroupOf E ≤ pPrimeCore p E := le_sSup ⟨hn, hc⟩
      simpa only [map_subgroupOf_eq_of_le hKE] using map_mono (f := E.subtype) hp
    intro x _
    obtain ⟨y, hy, he⟩ := hm x.property
    exact (Subtype.ext he : y = x) ▸ hy
  have he : pPrimeCore p E = ⊤ := top_unique hE
  have hc : Nat.Coprime p (Nat.card E) := by
    simpa only [he, card_top] using (pPrimeCore_coprime_card (p := p) (G := E))
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hc) hdiv

omit [Finite X] in
private theorem odd_element_normalizes {K : Subgroup X} (hK : K.IsCComponent)
    (horbit : ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2)
    (y : X) (hy : Odd (orderOf y)) : y ∈ normalizer (K : Set X) := by
  rcases horbit K hK with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    exact mem_top _
  · obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := y) (n := 2)
      (Nat.coprime_two_left.mpr hy)
    exact hk ▸ (normalizer (K : Set X)).pow_mem (sq_mem_of_index_two hi y) k

private theorem core_intersection_or_le {S K : Subgroup X}
    [Group.IsPerfect S] [IsSimpleGroup (S ⧸ pCore 2 S)]
    (hn : S ≤ normalizer (K : Set X)) : S ⊓ K ≤ S.pCoreIn 2 ∨ S ≤ K := by
  let : (K.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hn
  by_cases hle : S ≤ K
  · exact Or.inr hle
  left
  let N := K.subgroupOf S
  let q := QuotientGroup.mk' (pCore 2 S)
  have hnq : (N.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hN : N ≤ pCore 2 S := by
    rcases hnq.eq_bot_or_eq_top with hb | ht
    · intro x hx
      exact (QuotientGroup.eq_one_iff x).mp (mem_bot.mp (hb ▸ mem_map_of_mem q hx))
    · have hsup : N ⊔ pCore 2 S = ⊤ := by
        have he := congrArg (Subgroup.comap q) ht
        simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
      have htwo := isPGroup_quotient_of_sup_eq_top N (pCore 2 S) pCore_isPGroup hsup
      let := htwo.isNilpotent
      have he : N = ⊤ := top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
      exact (hle (subgroupOf_eq_top.mp he)).elim
  intro x hx
  exact mem_map_of_mem S.subtype (hN (show (⟨x,hx.1⟩ : S) ∈ K.subgroupOf S from hx.2))

private theorem plane_excludes_disjoint {p : ℕ} [Fact p.Prime]
    (C S K : Subgroup X) (hSC : S ≤ C) (hKC : K ≤ C)
    (hr : primeRank p X ≤ 2)
    (y : X) (hy : orderOf y = p) (hyC : y ∉ C)
    (a : X) (haS : a ∈ S) (ha : orderOf a = p) (hay : Commute a y)
    (hnS : S ≤ normalizer (K : Set X)) (hny : y ∈ normalizer (K : Set X))
    (hd : Disjoint (zpowers a) K) : Nat.Coprime p (Nat.card K) := by
  classical
  let A := zpowers a
  let Y := zpowers y
  have hAS : A ≤ S := zpowers_le.mpr haS
  have hAY : A ≤ centralizer (Y : Set X) := by
    apply zpowers_le.mpr
    apply mem_centralizer_iff.mpr
    rintro z ⟨j,rfl⟩
    exact (hay.zpow_right j).eq.symm
  have haX : orderOf a = p := ha
  let : IsElementaryAbelian p A := IsElementaryAbelian.zpowers_of_pow_eq_one
    (haX ▸ pow_orderOf_eq_one (a : X))
  let : IsElementaryAbelian p Y := IsElementaryAbelian.zpowers_of_pow_eq_one
    (hy ▸ pow_orderOf_eq_one y)
  have hYC : Disjoint Y C := by
    exact (C.disjoint_zpowers_of_prime_order_not_mem y hy hyC).symm
  let E := A ⊔ Y
  let : IsElementaryAbelian p E := IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp hAY)
  have hcard : Nat.card E = p ^ 2 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A Y
      ((le_centralizer_iff.mp hAY).trans (Subgroup.centralizer_le_normalizer _))
      (hYC.symm.mono_left (hAS.trans hSC)), Nat.card_zpowers, Nat.card_zpowers, haX, hy, pow_two]
  have hEK : Disjoint E K := by
    apply disjoint_def.mpr
    intro x hx hxK
    have hx' : x ∈ (A : Set X) * (Y : Set X) := by
      rw [← coe_mul_of_left_le_normalizer_right A Y
        (hAY.trans (Subgroup.centralizer_le_normalizer _))]
      exact hx
    obtain ⟨a', ha', y', hy', rfl⟩ := hx'
    have hy'C : y' ∈ C := by
      have hh := C.mul_mem (C.inv_mem (hSC (hAS ha'))) (hKC hxK)
      simpa only [inv_mul_cancel_left] using hh
    have hy'1 : y' = 1 := disjoint_def.mp hYC hy' hy'C
    simp only [hy'1, mul_one] at hxK ⊢
    exact disjoint_def.mp hd ha' hxK
  exact coprime_card_of_normalized_disjoint_plane hr E K hcard
    (sup_le (hAS.trans hnS) (zpowers_le.mpr hny)) hEK

private theorem perfect_normalizes {S K : Subgroup X} [Group.IsPerfect S]
    (hK : K.IsCComponent)
    (horbit : ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2) :
    S ≤ normalizer (K : Set X) := by
  rcases horbit K hK with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    exact le_top
  · let N := normalizer (K : Set X)
    let : N.Normal := N.normal_of_index_eq_two hi
    have hcard : Nat.card (X ⧸ N) = 2 := by
      change N.index = 2
      exact hi
    have htwo : IsPGroup 2 (X ⧸ N) :=
      IsPGroup.of_card (n := 1) (by simpa using hcard)
    let := htwo.isNilpotent
    exact (le_solvableResidual_of_isPerfect S).trans (solvableResidual_le_of_solvable_quotient N)

private theorem cComponent_inf_le_radical {K J : Subgroup X}
    (hK : K.IsCComponent) (hJ : J.IsCComponent) (hne : K ≠ J) :
    K ⊓ J ≤ solvableRadical X := by
  let q := QuotientGroup.mk' (solvableRadical X)
  have hfree := solvableRadical_quotient_solvableRadical (G := X)
  have hk := hK.map_quotient (solvableRadical X)
  have hj := hJ.map_quotient (solvableRadical X)
  have hcomm := hk.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hfree hj
    (fun he => hne (hK.eq_of_map_quotient_eq hJ _ he))
  have hcenter := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hfree hk.subnormal
  intro x hx
  have hxk : q x ∈ K.map q := mem_map.mpr ⟨x, hx.1, rfl⟩
  have hxj : q x ∈ J.map q := mem_map.mpr ⟨x, hx.2, rfl⟩
  have hz : (⟨q x, hxk⟩ : K.map q) ∈ center (K.map q) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact ((commutator_eq_bot_iff_le_centralizer.mp hcomm y.2) (q x) hxj).symm
  have he : (⟨q x, hxk⟩ : K.map q) = 1 := mem_bot.mp (hcenter ▸ hz)
  exact (QuotientGroup.eq_one_iff (N := solvableRadical X) x).mp
    (congrArg Subtype.val he)

/-- A nonsolvable subgroup lies in at most one C-component. -/
private theorem cComponent_unique_over_nonsolvable {B K J : Subgroup X}
    (hB : ¬ Group.IsSolvable B) (hK : K.IsCComponent) (hJ : J.IsCComponent)
    (hBK : B ≤ K) (hBJ : B ≤ J) : K = J := by
  by_contra hne
  have hBR := (le_inf hBK hBJ).trans (cComponent_inf_le_radical hK hJ hne)
  exact hB (Group.isSolvable_of_isSolvable_injective (inclusion_injective hBR))


/-- A faithful odd prime actor selects a normal component containing a perfect
subgroup with simple two-core quotient. Only a fixed prime element is needed;
the actor may act nontrivially on the two-core. -/
theorem normal_component_of_external_prime {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (C S : Subgroup X) [C.Normal]
    [Group.IsPerfect S] [IsSimpleGroup (S ⧸ pCore 2 S)]
    (hSC : S ≤ C) (hdE : p ∣ Nat.card (cComponentLayer C))
    (hr : primeRank p X ≤ 2)
    (y : X) (hy : orderOf y = p) (hyC : y ∉ C)
    (a : X) (haS : a ∈ S) (ha : orderOf a = p) (hay : Commute a y)
    (horbit : ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2) :
    ∃ K : Subgroup X, K ≤ C ∧ (K.subgroupOf C).IsCComponent ∧ S ≤ K ∧ K.Normal := by
  have hacore : a ∉ S.pCoreIn 2 := by
    intro haC
    have hc := (isPGroup_pCoreIn 2 S).orderOf_coprime hp.coprime_two_left ⟨a,haC⟩
    have hh : Nat.Coprime p p := by simpa only [Subgroup.orderOf_mk,ha] using hc
    exact (Fact.out : p.Prime).ne_one (by simpa using hh)
  have contains (K : Subgroup X) (hK : K.IsCComponent) (hKC : K ≤ C)
      (hdK : p ∣ Nat.card K) : S ≤ K := by
    have hnS : S ≤ normalizer (K : Set X) := perfect_normalizes hK horbit
    rcases core_intersection_or_le hnS with hc | hle
    · have haK : a ∉ K := fun hak => hacore (hc ⟨haS,hak⟩)
      have hd : Disjoint (zpowers a) K :=
        (K.disjoint_zpowers_of_prime_order_not_mem a ha haK).symm
      have hcop := plane_excludes_disjoint C S K hSC hKC hr y hy hyC a haS ha hay
        hnS (odd_element_normalizes hK horbit y (hy ▸ hp)) hd
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop hdK).elim
    · exact hle
  obtain ⟨J,hJ,hdJ⟩ := prime_component_in_layer hdE
  let K := J.map C.subtype
  have hKC : K ≤ C := map_subtype_le J
  have hK : K.IsCComponent := hJ.map_subtype (inferInstance : C.Normal).isSubnormal
  have hdK : p ∣ Nat.card K := by
    rwa [card_map_of_injective C.subtype_injective]
  have hSK : S ≤ K := contains K hK hKC hdK
  refine ⟨K,hKC,?_,hSK,?_⟩
  · change ((J.map C.subtype).comap C.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective C.subtype_injective]
    exact hJ
  · apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    let D := K.map (MulAut.conj g).toMonoidHom
    have hD : D.IsCComponent := hK.map_equiv (MulAut.conj g)
    have hDC : D ≤ C := by
      rintro x ⟨k,hk,rfl⟩
      exact (inferInstance : C.Normal).conj_mem k (hKC hk) g
    have hdD : p ∣ Nat.card D := by
      rwa [card_map_of_injective (MulAut.conj g).injective]
    have hSD : S ≤ D := contains D hD hDC hdD
    let : Nontrivial S := (QuotientGroup.mk'_surjective (pCore 2 S)).nontrivial
    exact mem_normalizer_iff_map_conj_eq.mpr
      (cComponent_unique_over_nonsolvable (Group.IsPerfect.not_isSolvable S) hD hK hSD hSK)

end Theory.GroupTheory.ExternalPrimeSelection
