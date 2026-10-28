module

public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductOrder
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.Frattini.BinarySquares

/-!
# Large extraspecial factors under a four-generator bound

In a finite two-group with cyclic center, a commuting normal supplement to
an extraspecial factor of order at least thirty-two is absorbed by that
factor if the ambient Frattini quotient has order at most sixteen.

If the supplement has trivial Frattini subgroup, it is elementary abelian,
central, and cyclic, so has order at most two and lies in the extraspecial
factor. Otherwise its mapped Frattini subgroup contains the shared central
involution. Every ambient square then lies in that mapped subgroup. The
central-product order formula and the properness of the supplement's
Frattini subgroup contradict the bound on the ambient Frattini quotient.
Finally, extraspecial squares are central, giving ambient order at most
thirty-two and hence equality. No elementary-rank bound or Hall type for
the supplement is required.

Source: the four-generator reduction in Janko–Thompson, Math. Z. 113
(1970), §4, printed p.389; the generator theorem is result 1.1 on p.385.
-/

open Subgroup

namespace Subgroup

/-- A four-generator two-group with cyclic center cannot have a proper
extraspecial central factor of order at least thirty-two. -/
public theorem eq_top_of_large_extraspecial_of_frattini_quotient_le_sixteen
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P)
    (hbound : Nat.card (P ⧸ frattini P) ≤ 16)
    (A D : Subgroup P) [A.Normal] [D.Normal] [IsExtraspecial 2 A]
    (hlarge : 32 ≤ Nat.card A)
    (hc : D ≤ centralizer (A : Set P)) (hg : A ⊔ D = ⊤) : A = ⊤ := by
  let : Fact (IsPGroup 2 D) := ⟨hP.to_subgroup D⟩
  by_cases hphi : frattini D = ⊥
  · let : IsElementaryAbelian 2 D :=
      (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
    have hDc : D ≤ center P := by
      have ht : (⊤ : Subgroup P) ≤ centralizer (D : Set P) := by
        rw [← hg]
        exact sup_le (le_centralizer_iff.mp hc)
          (le_centralizer_iff_isMulCommutative.mpr inferInstance)
      simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp ht
    let : IsCyclic D := isCyclic_of_le hDc
    have hDcard : Nat.card D ≤ 2 := by
      have h := IsElementaryAbelian.exponent_dvd_p 2 D
      rw [IsCyclic.exponent_eq_card] at h
      exact Nat.le_of_dvd (by decide) h
    have hDA : D ≤ A := by
      by_cases hD : D = ⊥
      · rw [hD]; exact bot_le
      · have heq : A ⊓ D = D := eq_of_le_of_card_ge inf_le_right (by
          rw [card_inf_eq_two_of_extraspecial_of_cyclic_center hP A D hD hc]
          exact hDcard)
        exact heq ▸ inf_le_left
    exact top_unique (hg ▸ sup_le le_rfl hDA)
  · let F := (frattini D).map D.subtype
    let : F.Normal := ConjAct.normal_of_characteristic_of_normal
    have hFne : F ≠ ⊥ := by
      intro h
      apply hphi
      apply map_injective D.subtype_injective
      simpa only [map_bot] using h
    have hFD : F ≤ D := map_subtype_le _
    have hi : A ⊓ F = (center A).map A.subtype := by
      apply eq_of_le_of_card_ge
      · rintro x ⟨ha, hf⟩
        exact ⟨⟨x, ha⟩, mem_center_iff.mpr
          (fun a => Subtype.ext (hc (hFD hf) a a.property)), rfl⟩
      · rw [card_map_of_injective A.subtype_injective,
          IsExtraspecial.center_order_p 2 A,
          card_inf_eq_two_of_extraspecial_of_cyclic_center hP A F hFne (hFD.trans hc)]
    have hZF : (center A).map A.subtype ≤ F := hi ▸ inf_le_right
    have hPhiF : frattini P ≤ F := by
      rw [hP.frattini_eq_closure_squares]
      apply (closure_le _).mpr
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_normal_right.mp (hg.symm ▸ mem_top x)
      change (a * d) ^ 2 ∈ F
      rw [(show Commute a d from hc hd a ha).mul_pow]
      apply F.mul_mem
      · exact hZF (mem_map_of_mem A.subtype
          (IsExtraspecial.square_mem_center (⟨a, ha⟩ : A)))
      · exact mem_map_of_mem D.subtype
          (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨d, hd⟩ : D))
    have hPhicard : Nat.card (frattini P) ≤ Nat.card (frattini D) := by
      simpa only [F, card_map_of_injective D.subtype_injective] using card_le_of_le hPhiF
    have hDne : D ≠ ⊥ := fun h => hFne (eq_bot_iff.mpr (h ▸ hFD))
    let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hDne
    have hPhilt : Nat.card (frattini D) < Nat.card D := by
      have hle := (frattini D).card_le_card_group
      apply lt_of_le_of_ne hle
      intro heq
      have ht := (frattini D).eq_top_of_card_eq heq
      have hb : (⊥ : Subgroup D) = ⊤ := frattini_nongenerating (by simpa using ht)
      exact bot_ne_top hb
    have hprod := card_mul_two_eq_of_extraspecial_of_cyclic_center hP A D hDne hc hg
    have hcard := card_eq_card_quotient_mul_card_subgroup (frattini P)
    have hsmall : Nat.card P ≤ 16 * Nat.card (frattini D) := by
      rw [hcard]
      exact Nat.mul_le_mul hbound hPhicard
    nlinarith

/-- A large extraspecial central factor and a four-generator bound identify
both the whole group and its exact order. -/
public theorem extraspecial_card_thirty_two_of_large_factor_of_frattini_quotient_le_sixteen
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P)
    (hbound : Nat.card (P ⧸ frattini P) ≤ 16)
    (A D : Subgroup P) [A.Normal] [D.Normal] [IsExtraspecial 2 A]
    (hlarge : 32 ≤ Nat.card A)
    (hc : D ≤ centralizer (A : Set P)) (hg : A ⊔ D = ⊤) :
    IsExtraspecial 2 P ∧ Nat.card P = 32 := by
  have hA := eq_top_of_large_extraspecial_of_frattini_quotient_le_sixteen
    hP hbound A D hlarge hc hg
  have he : IsExtraspecial 2 (⊤ : Subgroup P) := hA ▸ inferInstance
  let : IsExtraspecial 2 P := he.of_mulEquiv Subgroup.topEquiv
  have hPhiZ : frattini P ≤ center P := by
    rw [hP.frattini_eq_closure_squares]
    exact (closure_le _).mpr (by rintro _ ⟨x, rfl⟩; exact IsExtraspecial.square_mem_center x)
  have hPhiCard : Nat.card (frattini P) ≤ 2 := by
    simpa only [IsExtraspecial.center_order_p 2 P] using card_le_of_le hPhiZ
  have hcard := card_eq_card_quotient_mul_card_subgroup (frattini P)
  have hupper : Nat.card P ≤ 32 := by
    rw [hcard]
    exact Nat.mul_le_mul hbound hPhiCard
  have hlower := hlarge.trans A.card_le_card_group
  exact ⟨inferInstance, by omega⟩

end Subgroup
