module

public import BenderSuzuki.SE.Section11Lemma114Core
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import BenderSuzuki.External.Suzuki.V.proposition_1_2

/-!
# Section 11, Lemma 11.4: the degenerate Suzuki model

This file uses the root-subgroup and order calculations in
`MatrixGroups.SuzukiZero` to prove that every product of two distinct
involutions in `Sz(2)` has order five. It preserves the Section 11
cardinality theorem as a wrapper around the lower model theorem.
-/

noncomputable section

namespace BenderSuzuki

open _root_.BenderSuzuki.MatrixGroups PFAppendixIII External

universe u

/-- The degenerate concrete Suzuki group over `GF(2)` has order twenty. -/
public theorem lemma114_suzukiZero_card :
    Nat.card (SuzukiMatrixGroup 0) = 20 :=
  suzukiZero_card

private theorem suzukiZeroRootSubgroup_involution_eq_square
    {x : SuzukiMatrixGroup 0}
    (hxR : x ∈ suzukiZeroRootSubgroup)
    (hx : IsInvolution x) :
    x = suzukiZeroRootGenerator ^ 2 := by
  classical
  have hxmem : x ∈ Subgroup.zpowers suzukiZeroRootGenerator := by
    rw [← suzukiZeroRootSubgroup_eq_zpowers]
    exact hxR
  rw [mem_zpowers_iff_mem_range_orderOf,
    suzukiZeroRootGenerator_order] at hxmem
  rcases Finset.mem_image.mp hxmem with ⟨n, hn, hnx⟩
  have hnlt : n < 4 := Finset.mem_range.mp hn
  have hxorder : orderOf x = 2 :=
    orderOf_eq_prime hx.sq_eq_one hx.ne_one
  interval_cases n
  · have hxone : x = 1 := by simpa using hnx.symm
    exact (hx.ne_one hxone).elim
  · have hbad : (4 : ℕ) = 2 := by
      calc
        4 = orderOf suzukiZeroRootGenerator :=
          suzukiZeroRootGenerator_order.symm
        _ = orderOf x := congrArg orderOf (by simpa using hnx)
        _ = 2 := hxorder
    omega
  · exact hnx.symm
  · have hpowOrder :
        orderOf (suzukiZeroRootGenerator ^ 3) = 4 := by
      rw [orderOf_pow, suzukiZeroRootGenerator_order]
      norm_num
    have hbad : (4 : ℕ) = 2 := by
      calc
        4 = orderOf (suzukiZeroRootGenerator ^ 3) :=
          hpowOrder.symm
        _ = orderOf x := congrArg orderOf hnx
        _ = 2 := hxorder
    omega

private theorem lemma114_commuting_involutions_eq_of_sylow_unique
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (hunique : ∀ x y : Q, IsInvolution x → IsInvolution y → x = y)
    {u v : G} (hu : IsInvolution u) (hv : IsInvolution v)
    (huv : Commute u v) : u = v := by
  have huP : IsPGroup 2 (Subgroup.zpowers u) :=
    isPGroup_zpowers_of_involution hu
  have hvP : IsPGroup 2 (Subgroup.zpowers v) :=
    isPGroup_zpowers_of_involution hv
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor <;> intro hy
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, rfl⟩
      exact ⟨n, by rw [huv.zpow_zpow m n, mul_inv_cancel_right]⟩
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      change v ^ n = u ^ m * y * (u ^ m)⁻¹ at hn
      have hcomm := huv.zpow_zpow m n
      calc
        v ^ n = (u ^ m)⁻¹ * (u ^ m * v ^ n) := by group
        _ = (u ^ m)⁻¹ * (v ^ n * u ^ m) := by rw [hcomm.eq]
        _ = (u ^ m)⁻¹ * ((u ^ m * y * (u ^ m)⁻¹) * u ^ m) := by
          rw [hn]
        _ = y := by group
  have hsupP : IsPGroup 2
      (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' huP hvP hnorm
  obtain ⟨S, hsup_le_S⟩ := hsupP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have huS : u ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_left :
      Subgroup.zpowers u ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers u))
  have hvS : v ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_right :
      Subgroup.zpowers v ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers v))
  have hcoe : ((g • S : Sylow 2 G) : Subgroup G) = (Q : Subgroup G) :=
    congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
  let ug : Q := ⟨g * u * g⁻¹, by
    have hmem : g * u * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨u, huS, rfl⟩
    change g * u * g⁻¹ ∈ (Q : Subgroup G)
    simpa [hcoe] using hmem⟩
  let vg : Q := ⟨g * v * g⁻¹, by
    have hmem : g * v * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨v, hvS, rfl⟩
    change g * v * g⁻¹ ∈ (Q : Subgroup G)
    simpa [hcoe] using hmem⟩
  have hugAmbient : IsInvolution (g * u * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hu
  have hvgAmbient : IsInvolution (g * v * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hv
  have hug : IsInvolution ug := by
    constructor
    · intro h
      apply hugAmbient.ne_one
      simpa [ug] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [ug] using hugAmbient.sq_eq_one
  have hvg : IsInvolution vg := by
    constructor
    · intro h
      apply hvgAmbient.ne_one
      simpa [vg] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [vg] using hvgAmbient.sq_eq_one
  have heq : ug = vg := hunique ug vg hug hvg
  have hcoe' : g * u * g⁻¹ = g * v * g⁻¹ := congrArg Subtype.val heq
  simpa using (mul_left_cancel (mul_right_cancel hcoe'))

private theorem lemma114_suzukiZero_involution_product_order
    {s t : SuzukiMatrixGroup 0}
    (hs : IsInvolution s) (ht : IsInvolution t) (hst : s ≠ t) :
    orderOf (s * t) = 5 := by
  have hRcard : Nat.card suzukiZeroRootSubgroup = 4 :=
    suzukiZeroRootSubgroup_card
  have hRp : IsPGroup 2 suzukiZeroRootSubgroup := by
    apply IsPGroup.of_card
      (p := 2) (G := suzukiZeroRootSubgroup) (n := 2)
    simpa using hRcard
  have hRindex : suzukiZeroRootSubgroup.index = 5 := by
    have hmul := suzukiZeroRootSubgroup.card_mul_index
    rw [hRcard, lemma114_suzukiZero_card] at hmul
    omega
  have hRindexOdd : ¬ 2 ∣ suzukiZeroRootSubgroup.index := by
    rw [hRindex]
    norm_num
  let Q : Sylow 2 (SuzukiMatrixGroup 0) :=
    IsPGroup.toSylow hRp hRindexOdd
  have hQ : (Q : Subgroup (SuzukiMatrixGroup 0)) =
      suzukiZeroRootSubgroup := by
    dsimp only [Q]
    exact IsPGroup.toSylow_coe hRp hRindexOdd
  have hunique : ∀ x y : Q,
      IsInvolution x → IsInvolution y → x = y := by
    intro x y hx hy
    have hxAmbient : IsInvolution (x : SuzukiMatrixGroup 0) :=
      IsInvolution.map_of_injective hx
        (Q : Subgroup (SuzukiMatrixGroup 0)).subtype
        (Q : Subgroup (SuzukiMatrixGroup 0)).subtype_injective
    have hyAmbient : IsInvolution (y : SuzukiMatrixGroup 0) :=
      IsInvolution.map_of_injective hy
        (Q : Subgroup (SuzukiMatrixGroup 0)).subtype
        (Q : Subgroup (SuzukiMatrixGroup 0)).subtype_injective
    have hxR : (x : SuzukiMatrixGroup 0) ∈
        suzukiZeroRootSubgroup := by
      rw [← hQ]
      exact x.property
    have hyR : (y : SuzukiMatrixGroup 0) ∈
        suzukiZeroRootSubgroup := by
      rw [← hQ]
      exact y.property
    apply Subtype.ext
    exact
      (suzukiZeroRootSubgroup_involution_eq_square hxR hxAmbient).trans
        (suzukiZeroRootSubgroup_involution_eq_square hyR hyAmbient).symm
  have hprod_ne : s * t ≠ 1 := by
    intro hprod
    apply hst
    calc
      s = s * 1 := by simp
      _ = s * (s * t) := by rw [hprod]
      _ = t := by
        rw [← mul_assoc]
        have hss : s * s = 1 := by simpa [pow_two] using hs.sq_eq_one
        rw [hss, one_mul]
  have hnotEven : ¬ Even (orderOf (s * t)) := by
    intro heven
    rcases heven with ⟨m, hm⟩
    have horder : orderOf (s * t) = 2 * m := by
      simpa [two_mul] using hm
    obtain ⟨hw, hws, hwt⟩ :=
      External.Suzuki.V.suzuki_ch5_proposition_1_2_iii
        hs ht hst horder
    have hwsEq : (s * t) ^ m = s :=
      lemma114_commuting_involutions_eq_of_sylow_unique Q hunique hw hs hws
    have hwtEq : (s * t) ^ m = t :=
      lemma114_commuting_involutions_eq_of_sylow_unique Q hunique hw ht hwt
    exact hst (hwsEq.symm.trans hwtEq)
  have hodd : Odd (orderOf (s * t)) := Nat.not_even_iff_odd.mp hnotEven
  have hdivTwenty : orderOf (s * t) ∣ 20 := by
    simpa [lemma114_suzukiZero_card] using orderOf_dvd_natCard (s * t)
  have hdivFive : orderOf (s * t) ∣ 5 := by
    have hcop : Nat.Coprime (orderOf (s * t)) (2 ^ 2) :=
      hodd.coprime_two_right.pow_right 2
    apply hcop.dvd_of_dvd_mul_left
    simpa using hdivTwenty
  have horder_ne_one : orderOf (s * t) ≠ 1 := by
    intro horder
    exact hprod_ne (orderOf_eq_one_iff.mp horder)
  exact ((Nat.dvd_prime Nat.prime_five).mp hdivFive).resolve_left
    horder_ne_one

/-- Distinct involutions in the involution core of `Sz(2)` have product
order five. -/
public theorem lemma114_suzukiZeroCore_involution_product_order
    {s t : involutionCore (SuzukiMatrixGroup 0)}
    (hs : IsInvolution s) (ht : IsInvolution t) (hst : s ≠ t) :
    orderOf (s * t) = 5 := by
  have hsAmbient : IsInvolution (s : SuzukiMatrixGroup 0) :=
    IsInvolution.map_of_injective hs
      (involutionCore (SuzukiMatrixGroup 0)).subtype
      (involutionCore (SuzukiMatrixGroup 0)).subtype_injective
  have htAmbient : IsInvolution (t : SuzukiMatrixGroup 0) :=
    IsInvolution.map_of_injective ht
      (involutionCore (SuzukiMatrixGroup 0)).subtype
      (involutionCore (SuzukiMatrixGroup 0)).subtype_injective
  have hstAmbient : (s : SuzukiMatrixGroup 0) ≠ t := by
    intro h
    exact hst (Subtype.ext h)
  have horder :=
    lemma114_suzukiZero_involution_product_order
      hsAmbient htAmbient hstAmbient
  calc
    orderOf (s * t) =
        orderOf (((s * t : involutionCore (SuzukiMatrixGroup 0)) :
          SuzukiMatrixGroup 0)) :=
      (Subgroup.orderOf_coe (s * t)).symm
    _ = orderOf ((s : SuzukiMatrixGroup 0) *
        (t : SuzukiMatrixGroup 0)) := by rfl
    _ = 5 := horder

end BenderSuzuki
