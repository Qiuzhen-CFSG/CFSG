module

public import Theory.GroupTheory.PGroup.FusedFourCharacteristic
public import Theory.GroupTheory.PGroup.ExtraspecialDerivedSquares
public import Theory.GroupTheory.PGroup.OrderSixtyFourClassTwo
public import Theory.GroupTheory.PGroup.ExtraspecialAbelianIndexTwo

/-!
# Excluding a fused normal four above a minus-type extraspecial core

Let the Sylow two-subgroup have order 128, a unique central involution, and
no normal elementary eight. Suppose its unique normal elementary four lies
in an extraspecial subgroup of order 32, of elementary rank at most two,
with cyclic quotient of order four. The three involutions of the four cannot
all be fused in the ambient group.

The four-centralizer has order 64 and is nonabelian. Fusion excludes its
characteristic subgroups of order two. The derived-square obstruction for
an extraspecial core, followed by the core-local rank bound, puts its derived
group inside the central four. Noncommutativity and the absence of a
characteristic line make the derived group the whole four. The intrinsic
order-64 counting lemma makes the center that same four, so all squares
belong to the core. But the centralizer surjects onto the cyclic quotient of
order four, a contradiction.

No elementary-rank bound on the whole Sylow subgroup is used. Simplicity,
nonsolvability, and the N₂ hypothesis are unnecessary for this exclusion.

Source: Janko–Thompson, Math. Z. 113 (1970), printed p.389, invoking
results 1.3–1.5 on printed p.386. The characteristic-subgroup counting
argument here replaces the classification invocation in this specialization.
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition.NormalEightOrder128FusedFour

/-- Fusion of the unique normal four is impossible above a rank-two
extraspecial core with cyclic quotient of order four. -/
public theorem false_of_fused_normal_four
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : Nat.card S = 128)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (H : Subgroup S) [H.Normal] [IsExtraspecial 2 H]
    (hH : Nat.card H = 32) (hWH : W ≤ H)
    (hiH : H.index = 4) [IsCyclic (S ⧸ H)]
    (hcoreRank : ∀ E : Subgroup H, IsElementaryAbelian 2 E → Nat.card E < 8)
    (hfused : ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    False := by
  let C := centralizer (W : Set S)
  have hiC : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      S.isPGroup' hZ W hW
  let : C.Normal := normal_of_index_eq_two hiC
  have hC : Nat.card C = 64 := by
    have hh := C.card_mul_index
    rw [hiC, hS] at hh
    omega
  have hchar : ∀ K : Subgroup C, K.Characteristic → Nat.card K ≠ 2 := by
    intro K hK
    let : K.Characteristic := hK
    exact S.centralizer_fused_four_no_characteristic_two hno hZ W hW hunique hfused K
  have helem : ∀ K : Subgroup C, K.Characteristic → IsElementaryAbelian 2 K →
      Nat.card K < 8 := by
    intro K hK he
    let : K.Characteristic := hK
    let : IsElementaryAbelian 2 K := he
    exact S.centralizer_four_characteristic_elementary_card_lt_eight hno W K
  have hnot : ¬ H ≤ C := by
    intro hHC
    have hcenter : W.subgroupOf H ≤ center H := by
      intro w hw
      apply mem_center_iff.mpr
      intro h
      exact Subtype.ext ((hHC h.property) w hw).symm
    have hc := card_le_of_le hcenter
    rw [Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv, hW,
      IsExtraspecial.center_order_p 2 H] at hc
    omega
  have hnonab : ¬ IsMulCommutative C := by
    intro hab
    let : IsMulCommutative C := hab
    let B := C.subgroupOf H
    have hiB : B.index = 2 := by
      have hd : C.relIndex H ∣ 2 := by
        simpa only [hiC] using (relIndex_dvd_index_of_normal (H := C) (K := H))
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact (hnot (relIndex_eq_one.mp h)).elim
      · exact h
    have hZB : center H ≤ B := by
      intro h hh w hw
      exact congrArg Subtype.val (mem_center_iff.mp hh (⟨w, hWH hw⟩ : H))
    exact IsExtraspecial.not_isMulCommutative_of_index_two (by omega) B hiB hZB
      (C.comap_injective_isMulCommutative H.subtype_injective)
  have hWC : W ≤ C := le_centralizer W
  let F := W.subgroupOf C
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hWC
  have hF : Nat.card F = 4 := (Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv).trans hW
  have hFZ : F ≤ center C := by
    intro w hw
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property w hw).symm
  have hderH : (commutator C).map C.subtype ≤ H := by
    rw [map_subtype_commutator]
    exact (commutator_mono le_top le_top).trans
      (Normal.quotient_commutative_iff_commutator_le.mp inferInstance)
  have hderF : commutator C ≤ F := by
    intro x hx
    have hxH : (x : S) ∈ H := hderH (mem_map_of_mem C.subtype hx)
    let E := W.subgroupOf H
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hWH
    have hE : Nat.card E = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv).trans hW
    have hx2 : x ^ 2 = 1 :=
      derived_square_eq_one_of_no_characteristic_two_of_normal_extraspecial H C hchar x hx
    have hm := mem_four_of_square_eq_one_of_elementary_card_lt_eight hcoreRank E hE
      (show (⟨x, hxH⟩ : H) ^ 2 = 1 from Subtype.ext (congrArg (fun a : C => (a : S)) hx2))
      (show (⟨x, hxH⟩ : H) ∈ centralizer (E : Set H) from by
        intro w hw
        exact Subtype.ext (x.property w hw))
    exact hm
  let : IsElementaryAbelian 2 (commutator C) := {
    toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
      (congrArg (fun a : F => (a : C)) (mul_comm' (⟨a, hderF a.property⟩ : F)
        (⟨b, hderF b.property⟩ : F)))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : C) (hderF x.property)) }
  have hder : Nat.card (commutator C) = 4 := by
    have hd : Nat.card (commutator C) ∣ 4 := hF ▸ card_dvd_of_le hderF
    have hn2 := hchar (commutator C) inferInstance
    have hn1 : Nat.card (commutator C) ≠ 1 := fun h =>
      hnonab ((commutator_eq_bot_iff C).mp (card_eq_one.mp h))
    have hp := Nat.card_pos (α := commutator C)
    have hl := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases Nat.card (commutator C) <;> omega
  have hclass : commutator C ≤ center C := hderF.trans hFZ
  obtain ⟨hcZ, _⟩ := OrderSixtyFourClassTwo.center_elementary_four hC hclass hder
    (by have hh := card_le_of_le hFZ; omega) hchar helem
  have hFcenter : F = center C := eq_of_le_of_card_ge hFZ (by omega)
  have hsq (x : C) : (x : S) ^ 2 ∈ W := by
    have hcentral : x ^ 2 ∈ center C := by
      apply mem_center_iff.mpr
      intro y
      have hxy := commutator_mem_commutator (mem_top x) (mem_top y)
      have hcent := hclass hxy
      have hs : ⁅x,y⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := commutator C) _ hxy
      have hh : ⁅x ^ 2,y⁆ = 1 := by
        rw [pow_two, commutatorElement_mul_left_eq_conj_mul,
          mem_center_iff.mp hcent x, mul_inv_cancel_right, ← pow_two, hs]
      exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
    rw [← hFcenter] at hcentral
    exact hcentral
  let q := QuotientGroup.mk' H
  have hquot : Nat.card (S ⧸ H) = 4 := by rw [← index_eq_card, hiH]
  obtain ⟨v, hv⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S ⧸ H)
  rw [hquot] at hv
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H v
  have hlift : ∃ c : C, q c = q g := by
    by_cases hg : g ∈ C
    · exact ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨h, hh, hhC⟩ := SetLike.not_le_iff_exists.mp hnot
    have hhg : h * g ∈ C := (C.mul_mem_iff_of_index_two hiC).mpr
      (by simp only [hhC, hg])
    refine ⟨⟨h * g, hhg⟩, ?_⟩
    change q (h * g) = q g
    have hhq : q h = 1 := (QuotientGroup.eq_one_iff h).mpr hh
    rw [map_mul, hhq, one_mul]
  obtain ⟨c, hc⟩ := hlift
  have hc2 : (q g) ^ 2 = 1 := by
    rw [← hc, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hWH (hsq c))
  have hd := orderOf_dvd_iff_pow_eq_one.mpr hc2
  rw [hv] at hd
  norm_num at hd

end Stellmacher.Recognition.NormalEightOrder128FusedFour
