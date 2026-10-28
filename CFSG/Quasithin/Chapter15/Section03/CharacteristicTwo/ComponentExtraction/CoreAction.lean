module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Candidates

/-!
# The three-prime core of the selected component

The candidate's three-prime core lies in the actual action kernel and hence
in `M_I`. Since `Y₊ = θ(M_I)`, this core normalizes `Y₊`. Its intersection
with `Y₊` is a two-group: its image in `Y₊/O₂(Y₊)` has both three-power
order and order prime to three. Relative normality puts that intersection
in `O₂(L)`. Thus `[O₃′(L),Y₊] ≤ O₂(L)`.

The three-subgroups lemma, applied inside `LY₊/O₂(L)`, and `L=[L,Y₊]`
then put the image of `O₃′(L)` in the center of `L/O₂(L)`. This proves
the core-action step without classifying that quotient. The SQTK
classification is still needed to conclude quasisimplicity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.15(2) and 15.3.26(2), printed pp.1125 and 1130.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem inf_le_core_of_coprime {Y N : Subgroup G}
    (hN : Nat.Coprime 3 (Nat.card N))
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y)) : N ⊓ Y ≤ Y.pCoreIn 2 := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  let y : Y := ⟨x, hx.2⟩
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hcop : Nat.Coprime 3 (orderOf y) := by
    rw [← Subgroup.orderOf_coe y]
    exact hN.of_dvd_right (N.orderOf_dvd_natCard hx.1)
  have hqy : q y = 1 := by
    obtain ⟨n, hn⟩ := hY.exists_orderOf_eq_pow (q y)
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (hcop.pow_left n)
      (hn ▸ dvd_refl _) (orderOf_map_dvd q y)
  exact ⟨y, (QuotientGroup.eq_one_iff _).mp hqy, rfl⟩

omit [Finite G] in
private theorem commutator_le_of_generated (Q L Y N : Subgroup G) [Q.Normal]
    (hgen : L = ⁅L, Y⁆) (hn : ⁅N, L⁆ ≤ N) (hcomm : ⁅N, Y⁆ ≤ Q) :
    ⁅N, L⁆ ≤ Q := by
  let q := QuotientGroup.mk' Q
  have hNY : ⁅N.map q, Y.map q⁆ = ⊥ := by
    rw [← map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, QuotientGroup.ker_mk'] using hcomm
  have hNL : ⁅N.map q, L.map q⁆ ≤ N.map q := by
    rw [← map_commutator]
    exact map_mono hn
  have hrot₁ : ⁅⁅Y.map q, N.map q⁆, L.map q⁆ = ⊥ := by
    rw [commutator_comm (Y.map q), hNY, commutator_bot_left]
  have hrot₂ : ⁅⁅N.map q, L.map q⁆, Y.map q⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hNL le_rfl).trans_eq hNY)
  have hc := commutator_commutator_eq_bot_of_rotate hrot₁ hrot₂
  rw [← map_commutator, ← hgen, commutator_comm, ← map_commutator] at hc
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hc

namespace StarComponentCandidate
variable {d : LocalData G} {I : Subgroup G}

/-- The core-action containment in the proof of 15.3.15(2). -/
theorem threePrimeCore_commutator_le_twoCore (c : StarComponentCandidate d I)
    (hI : I ∈ d.Hplus) (hθ : theta (d.MI I) = d.Yplus)
    (hindex : (normalizer (c.L : Set G)).relIndex I ≤ 2)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus)) :
    ⁅(pPrimeCore 3 c.L).map c.L.subtype, d.Yplus⁆ ≤ c.L.pCoreIn 2 := by
  let N := (pPrimeCore 3 c.L).map c.L.subtype
  have hYI : d.Yplus ≤ I := le_sup_left.trans hI.1.2
  have hYL : d.Yplus ≤ normalizer (c.L : Set G) :=
    ComponentIntersection.normalizes_of_index_le_two hYI
      (hθ ▸ ComponentIntersection.theta_isPPerfect (d.MI I)) hindex
  have hLN : c.L ≤ normalizer (N : Set G) :=
    c.L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image c.L (pPrimeCore 3 c.L))
  have hYN : d.Yplus ≤ normalizer (N : Set G) :=
    hYL.trans (normalizer_le_normalizer_characteristic_image c.L (pPrimeCore 3 c.L))
  have hNY : N ≤ normalizer (d.Yplus : Set G) := by
    rw [← hθ]
    exact (c.threePrimeCore_le_actionKernel.trans hC).trans
      ((d.MI I).le_normalizer.trans (normalizer_le_normalizer_theta (d.MI I)))
  have hNcop : Nat.Coprime 3 (Nat.card N) := by
    rw [show Nat.card N = Nat.card (pPrimeCore 3 c.L) from card_map_of_injective c.L.subtype_injective]
    exact pPrimeCore_coprime_card
  have htwo : IsPGroup 2 (N ⊓ d.Yplus : Subgroup G) :=
    (isPGroup_pCoreIn 2 d.Yplus).to_le (inf_le_core_of_coprime hNcop hY)
  have hnorm : N ≤ normalizer ((N ⊓ d.Yplus : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro n hn x hx
    exact ⟨(N.le_normalizer hn x).mp hx.1, (hNY hn x).mp hx.2⟩
  have hcore := le_pCoreIn_of_normalizes htwo inf_le_left hnorm
  have hNL : N ≤ c.L := map_subtype_le _
  have hcores : N.pCoreIn 2 ≤ c.L.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn N c.L 2 hNL
      (normal_subgroupOf_of_le_normalizer hLN).isSubnormal
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hYN)
    (le_normalizer_iff_commutator_le_right.mp hNY)).trans (hcore.trans hcores)

/-- Commutator generation makes the three-prime core central modulo the two-core. -/
theorem threePrimeCore_central_mod_twoCore (c : StarComponentCandidate d I)
    (hI : I ∈ d.Hplus) (hθ : theta (d.MI I) = d.Yplus)
    (hindex : (normalizer (c.L : Set G)).relIndex I ≤ 2)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hNorm : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus)) :
    ⁅(pPrimeCore 3 c.L).map c.L.subtype, c.L⁆ ≤ c.L.pCoreIn 2 := by
  let N := (pPrimeCore 3 c.L).map c.L.subtype
  let H := c.L ⊔ d.Yplus
  have hLH : c.L ≤ H := le_sup_left
  have hYH : d.Yplus ≤ H := le_sup_right
  have hNH : N ≤ H := (map_subtype_le _).trans hLH
  have hQH : c.L.pCoreIn 2 ≤ H := (pCoreIn_le _ _).trans hLH
  have hYL : d.Yplus ≤ normalizer (c.L : Set G) :=
    ComponentIntersection.normalizes_of_index_le_two (le_sup_left.trans hI.1.2)
      (hθ ▸ ComponentIntersection.theta_isPPerfect (d.MI I)) hindex
  have hHL : H ≤ normalizer (c.L : Set G) := sup_le c.L.le_normalizer hYL
  let _ : ((c.L.pCoreIn 2).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer
      (hHL.trans (normalizer_le_normalizer_characteristic_image c.L (pCore 2 c.L)))
  let _ : (N.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer
      (hHL.trans (normalizer_le_normalizer_characteristic_image c.L (pPrimeCore 3 c.L)))
  have hgen : c.L = ⁅c.L, d.Yplus⁆ :=
    d.thompson_component_eq_commutator_of_orbit hI c.le_thompson c.component
      hθ hindex c.outside hC hNorm c.star_quasisimple
  have hgenH : c.L.subgroupOf H = ⁅c.L.subgroupOf H, d.Yplus.subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    simpa only [map_commutator, map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le hYH] using hgen
  have hcomm : ⁅N, d.Yplus⁆ ≤ c.L.pCoreIn 2 :=
    c.threePrimeCore_commutator_le_twoCore hI hθ hindex hC hY
  have hcommH : ⁅N.subgroupOf H, d.Yplus.subgroupOf H⁆ ≤
      (c.L.pCoreIn 2).subgroupOf H := by
    intro x hx
    have hh := mem_map_of_mem H.subtype hx
    rw [map_commutator, map_subgroupOf_eq_of_le hNH,
      map_subgroupOf_eq_of_le hYH] at hh
    exact hcomm hh
  have hresult := commutator_le_of_generated ((c.L.pCoreIn 2).subgroupOf H)
    (c.L.subgroupOf H) (d.Yplus.subgroupOf H) (N.subgroupOf H) hgenH
    (commutator_le_left _ _) hcommH
  have hm := map_mono (f := H.subtype) hresult
  simpa only [map_commutator, map_subgroupOf_eq_of_le hNH,
    map_subgroupOf_eq_of_le hLH, map_subgroupOf_eq_of_le hQH] using hm

/-- The centrality assertion in the intrinsic two-core quotient. -/
theorem threePrimeCore_image_le_center (c : StarComponentCandidate d I)
    (hI : I ∈ d.Hplus) (hθ : theta (d.MI I) = d.Yplus)
    (hindex : (normalizer (c.L : Set G)).relIndex I ≤ 2)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hNorm : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus)) :
    (pPrimeCore 3 c.L).map (QuotientGroup.mk' (pCore 2 c.L)) ≤
      center (c.L ⧸ pCore 2 c.L) := by
  have hc := c.threePrimeCore_central_mod_twoCore hI hθ hindex hC hNorm hY
  have hi : ⁅pPrimeCore 3 c.L, (⊤ : Subgroup c.L)⁆ ≤ pCore 2 c.L := by
    intro x hx
    have hm := mem_map_of_mem c.L.subtype hx
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm
    obtain ⟨y, hy, he⟩ := hc hm
    exact (Subtype.ext he : y = x) ▸ hy
  apply commutator_top_right_eq_bot_iff_le_center.mp
  rw [← (QuotientGroup.mk' (pCore 2 c.L)).range_eq_top.mpr
    (QuotientGroup.mk'_surjective _), MonoidHom.range_eq_map, ← map_commutator]
  apply (Subgroup.map_eq_bot_iff _).mpr
  simpa only [QuotientGroup.ker_mk'] using hi

end StarComponentCandidate
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo

end
