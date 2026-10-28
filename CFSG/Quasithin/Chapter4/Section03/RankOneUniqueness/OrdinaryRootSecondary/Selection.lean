module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo
public import Theory.GroupTheory.RankTwoDisjointAction
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.PPrimeCore

/-!
# Selecting the secondary component with an external scalar

A simple perfect subgroup in the component layer is contained in a component
whose order has the chosen odd prime divisor. The faithful scalar and a Levi
prime element form an elementary plane disjoint from any candidate component
not containing the Levi. The rank bound excludes that possibility. Applying
the same argument to every conjugate gives normality, including the possible
two-component orbit of source 1.2.2.

Source: Aschbacher--Smith 1.2.1--2 and 4.3.6, printed pp.504--505, 614--615.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootSecondary
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

omit [Finite X] in
private theorem simple_disjoint_or_le {S K : Subgroup X} [IsSimpleGroup S]
    (hn : S ≤ normalizer (K : Set X)) : Disjoint S K ∨ S ≤ K := by
  let : (K.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hn
  rcases (inferInstance : (K.subgroupOf S).Normal).eq_bot_or_eq_top with hb | ht
  · left
    apply disjoint_def.mpr
    intro x hxS hxK
    have hx : (⟨x, hxS⟩ : S) = 1 := mem_bot.mp (hb ▸ hxK)
    exact congrArg Subtype.val hx
  · right
    intro x hx
    exact (show (⟨x, hx⟩ : S) ∈ K.subgroupOf S from ht ▸ mem_top _)

private theorem plane_excludes_disjoint {p : ℕ} [Fact p.Prime]
    (C S K : Subgroup X) (hSC : S ≤ C) (hKC : K ≤ C)
    (hr : primeRank p X ≤ 2) (hdS : p ∣ Nat.card S)
    (y : X) (hy : orderOf y = p) (hyC : y ∉ C)
    (hyS : y ∈ centralizer (S : Set X))
    (hnS : S ≤ normalizer (K : Set X)) (hny : y ∈ normalizer (K : Set X))
    (hd : Disjoint S K) : Nat.Coprime p (Nat.card K) := by
  classical
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hdS
  let A := zpowers (a : X)
  let Y := zpowers y
  have hAS : A ≤ S := zpowers_le.mpr a.property
  have hAY : A ≤ centralizer (Y : Set X) :=
    le_centralizer_iff.mp ((show Y ≤ centralizer (S : Set X) from
      zpowers_le.mpr hyS).trans (centralizer_le hAS))
  have haX : orderOf (a : X) = p := (orderOf_injective S.subtype S.subtype_injective a).trans ha
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
    exact disjoint_def.mp hd (hAS ha') hxK
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

/-- A faithful external prime-order scalar selects a unique normal component
containing a simple perfect subgroup of the centralizer's component layer.
The proof uses the actual rank-three obstruction, including the nonnormal
two-component orbit from source 1.2.2. -/
theorem normal_component_of_external_scalar {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (C S : Subgroup X) [C.Normal]
    [IsSimpleGroup S] [Group.IsPerfect S]
    (hSC : S ≤ C) (hSlayer : S.subgroupOf C ≤ cComponentLayer C)
    (hdS : p ∣ Nat.card S) (hr : primeRank p X ≤ 2)
    (y : X) (hy : orderOf y = p) (hyC : y ∉ C)
    (hyS : y ∈ centralizer (S : Set X))
    (horbit : ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2) :
    ∃ K : Subgroup X, K ≤ C ∧ (K.subgroupOf C).IsCComponent ∧ S ≤ K ∧ K.Normal := by
  have hdE : p ∣ Nat.card (cComponentLayer C) := by
    have hd : Nat.card S ∣ Nat.card (cComponentLayer C) := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv]
      exact card_dvd_of_le hSlayer
    exact hdS.trans hd
  obtain ⟨J, hJ, hdJ⟩ := prime_component_in_layer hdE
  let K := J.map C.subtype
  have hKC : K ≤ C := map_subtype_le J
  have hK : K.IsCComponent := hJ.map_subtype (inferInstance : C.Normal).isSubnormal
  have hdK : p ∣ Nat.card K := by
    rwa [card_map_of_injective C.subtype_injective]
  have hSK : S ≤ K := by
    rcases simple_disjoint_or_le (perfect_normalizes (S := S) hK horbit) with hd | hle
    · have hc := plane_excludes_disjoint C S K hSC hKC hr hdS y hy hyC hyS
        (perfect_normalizes hK horbit)
        (odd_element_normalizes hK horbit y (hy ▸ hp)) hd
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hc hdK).elim
    · exact hle
  refine ⟨K, hKC, ?_, hSK, ?_⟩
  · change ((J.map C.subtype).comap C.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective C.subtype_injective]
    exact hJ
  · apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    let D := K.map (MulAut.conj g).toMonoidHom
    have hD : D.IsCComponent := hK.map_equiv (MulAut.conj g)
    have hDC : D ≤ C := by
      rintro x ⟨k, hk, rfl⟩
      exact (inferInstance : C.Normal).conj_mem k (hKC hk) g
    have hdD : p ∣ Nat.card D := by
      rwa [card_map_of_injective (MulAut.conj g).injective]
    have hSD : S ≤ D := by
      rcases simple_disjoint_or_le (perfect_normalizes (S := S) hD horbit) with hd | hle
      · have hc := plane_excludes_disjoint C S D hSC hDC hr hdS y hy hyC hyS
          (perfect_normalizes hD horbit)
          (odd_element_normalizes hD horbit y (hy ▸ hp)) hd
        exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hc hdD).elim
      · exact hle
    exact mem_normalizer_iff_map_conj_eq.mpr
      (Chapter1.Section02.IndexTwo.cComponent_unique_over_nonsolvable
        (Group.IsPerfect.not_isSolvable S) hD hK hSD hSK)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootSecondary
