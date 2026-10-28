module

public import Theory.GroupTheory.PGroup.SymplecticSixteenFactors
public import Theory.ElementaryAbelian.ExtraspecialCardBound

/-!
# Intrinsic geometry of symplectic groups of order sixteen

For a symplectic two-group of order sixteen with cyclic center which is not
itself a Hall factor, the center has order four and every elementary subgroup
has order less than eight. No ambient elementary-rank hypothesis is used.

The extraspecial pairing bound gives rank at most two in the extraspecial
factor, so its classification forces order eight. The central-product order
formula leaves a commuting factor of order four, which is the whole center.
An elementary eight together with this cyclic center would generate the group
and centralize the eight, forcing the eight into the cyclic center.

Source: Hall's decomposition and Janko–Thompson, Math. Z. 113 (1970), §4,
printed pp.392–393; the pairing estimate is `extraspecial_two_elementary_card_sq_le`.
-/

open Subgroup

private theorem extraspecial_rank_small {A : Type*} [Group A] [Finite A] [IsExtraspecial 2 A]
    (hcard : Nat.card A ≤ 16) :
    ∀ E : Subgroup A, IsElementaryAbelian 2 E → Nat.card E < 8 := by
  intro E hE
  let : IsElementaryAbelian 2 E := hE
  let : IsElementaryAbelian 2 (center A) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [IsExtraspecial.center_order_p 2 A] using pow_card_eq_one' (x := z) }
  let : IsElementaryAbelian 2 (E ⊔ center A : Subgroup A) :=
    IsElementaryAbelian.sup_of_le_centralizer (center_le_centralizer _)
  have hb := extraspecial_two_elementary_card_sq_le (E ⊔ center A) le_sup_right
  have he := card_le_of_le (show E ≤ E ⊔ center A from le_sup_left)
  nlinarith

/-- The cyclic center of a non-Hall symplectic group of order sixteen has order four. -/
public theorem IsBinarySymplecticType.center_card_eq_four_of_card_sixteen
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (hcard : Nat.card P = 16)
    (hsymp : IsBinarySymplecticType P) (hnot : ¬ IsBinaryHallFactor P) :
    Nat.card (center P) = 4 := by
  obtain ⟨A, D, hAn, hDn, hA, hD, hc, hgen⟩ := hsymp.exists_normal_factors
  have he : IsExtraspecial 2 A := by
    rcases hA with hA | hA
    · have hDt : D = ⊤ := by simpa only [hA, bot_sup_eq] using hgen
      exact (hnot (hD.of_mulEquiv
        ((MulEquiv.subgroupCongr hDt).trans Subgroup.topEquiv))).elim
    · exact hA
  let : A.Normal := hAn
  let : D.Normal := hDn
  let : IsExtraspecial 2 A := he
  have hmodel : IsRankTwoExtraspecialModel A :=
    IsExtraspecial.rank_two_classification (extraspecial_rank_small (A.card_le_card_group.trans (by omega)))
  have hAc : Nat.card A = 8 ∧ IsBinaryHallFactor A := by
    rcases hmodel.card_eight_hall_or_thirty_two with h | h
    · exact h
    · have hh := A.card_le_card_group
      omega
  have hDne : D ≠ ⊥ := by
    intro hDbot
    have hAt : A = ⊤ := by simpa only [hDbot, sup_bot_eq] using hgen
    exact hnot (hAc.2.of_mulEquiv
      ((MulEquiv.subgroupCongr hAt).trans Subgroup.topEquiv))
  have hprod := card_mul_two_eq_of_extraspecial_of_cyclic_center hP A D hDne hc hgen
  have hDc : Nat.card D = 4 := by rw [hcard, hAc.1] at hprod; omega
  let : IsMulCommutative D :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hDc)
  have hcentral : D ≤ center P := by
    have hall : (⊤ : Subgroup P) ≤ centralizer (D : Set P) := by
      rw [← hgen]
      exact sup_le (le_centralizer_iff.mp hc) (le_centralizer D)
    simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp hall
  have hinter := card_inf_eq_two_of_extraspecial_of_cyclic_center hP A D hDne hc
  have hZA : (center A).map A.subtype ≤ D := by
    have hle : A ⊓ D ≤ (center A).map A.subtype := by
      intro x hx
      refine ⟨⟨x, hx.1⟩, mem_center_iff.mpr ?_, rfl⟩
      intro a
      exact Subtype.ext (hc hx.2 a a.property)
    have heq : A ⊓ D = (center A).map A.subtype :=
      eq_of_le_of_card_ge hle (by
        rw [card_map_of_injective A.subtype_injective,
          IsExtraspecial.center_order_p 2 A, hinter])
    rw [← heq]
    exact inf_le_right
  have hcenter : D = center P := (center_eq_of_central_product D A hcentral
    ((sup_comm D A).trans hgen) hZA).symm
  exact hcenter ▸ hDc

/-- A group of order sixteen with cyclic center of order four has elementary rank at most two. -/
public theorem Subgroup.elementary_card_lt_eight_of_card_sixteen_center_four {P : Type*} [Group P] [Finite P]
    [IsCyclic (center P)] (hcard : Nat.card P = 16) (hZ : Nat.card (center P) = 4) :
    ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8 := by
  intro E hE
  let : IsElementaryAbelian 2 E := hE
  by_contra! hbig
  have hnot : ¬ center P ≤ E := by
    intro h
    have hd : Nat.card (center P) ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro z
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := E) (z : P) (h z.property))
    rw [hZ] at hd
    norm_num at hd
  have hstrict : E < E ⊔ center P := lt_of_le_of_ne le_sup_left (fun h => hnot (h ▸ le_sup_right))
  have hlt : Nat.card E < Nat.card (E ⊔ center P : Subgroup P) :=
    lt_of_not_ge (fun h => hstrict.ne (eq_of_le_of_card_ge le_sup_left h))
  have hdiv : Nat.card (E ⊔ center P : Subgroup P) ∈ Nat.divisors 16 := by
    apply Nat.mem_divisors.mpr
    exact ⟨hcard ▸ (E ⊔ center P).card_subgroup_dvd_card, by decide⟩
  have htop : E ⊔ center P = ⊤ := by
    apply eq_top_of_card_eq
    rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    omega
  have hcentral : E ≤ center P := by
    have hall : (⊤ : Subgroup P) ≤ centralizer (E : Set P) := by
      rw [← htop]
      exact sup_le (le_centralizer E) (center_le_centralizer _)
    simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp hall
  let : IsCyclic E := isCyclic_of_le hcentral
  have hd := IsElementaryAbelian.exponent_dvd_p 2 E
  rw [IsCyclic.exponent_eq_card] at hd
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega
