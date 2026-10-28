module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Action

/-!
# The original F₁ has the full five-normalizer image

The actual complement A has image outside the image of S: otherwise
T=AQ₅S would force T≤QS=R₁, contradicting the original source orders.
Its image also contains the central involution coming from Uα≤W≤A.
Inside the five-normalizer this forces image order four. Adjoining the
original five-subgroup therefore gives the entire normalizer of order twenty.

Source: Aschbacher–Smith, J.4.4(3), printed p.441. Both quotient maps and
the complement preimage are unchanged from the original local setup.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)

private abbrev star (B:Subgroup G) : Subgroup S5 :=
  (B.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap

private theorem star_sup (B C:Subgroup G) (hB:B≤d.toTypeRuSetup.H) (hC:C≤d.toTypeRuSetup.H) :
    star (d:=d) (B⊔C)=star (d:=d) B⊔star (d:=d) C := by
  rw [star,subgroupOf_sup hB hC,Subgroup.map_sup]

private theorem star_mono {B C:Subgroup G} (h:B≤C) : star (d:=d) B≤star (d:=d) C :=
  map_mono (fun _ hx=>h hx)

private theorem star_Q : star (d:=d) d.toTypeRuSetup.Q=⊥ := by
  change (d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap=⊥
  rw [←d.ru2.quotient_kernel,Subgroup.map_ker_self]

private theorem star_Q₅ (B5:Sylow 5 d.toTypeRuSetup.H) : star (d:=d) (Q₅ d B5)=⊥ :=
  bot_unique ((star_mono (Q₅_le_Q d B5)).trans_eq star_Q)

private theorem star_B5 (B5:Sylow 5 d.toTypeRuSetup.H) :
    star (d:=d) (B5Image B5)=B5.map d.ru2.quotientMap := by
  change (((B5:Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype).comap
    d.toTypeRuSetup.H.subtype).map d.ru2.quotientMap=_
  rw [comap_map_eq_self_of_injective d.toTypeRuSetup.H.subtype_injective]

private theorem star_S_not_top (_B5:Sylow 5 d.toTypeRuSetup.H) :
    ¬star (d:=d) (d.T:Subgroup G)≤star (d:=d) d.toTypeRuSetup.S := by
  intro h
  have hQS : d.toTypeRuSetup.Q⊔d.toTypeRuSetup.S=d.toTypeRuSetup.R₁ :=
    d.Q_sup_S_eq_parabolic_core.trans d.parabolic_core_eq_R₁
  have hQR : d.toTypeRuSetup.Q≤d.toTypeRuSetup.R₁ := hQS ▸ le_sup_left
  have hSR : d.toTypeRuSetup.S≤d.toTypeRuSetup.R₁ := hQS ▸ le_sup_right
  have hT : (d.T:Subgroup G)≤d.toTypeRuSetup.R₁ := by
    intro t ht
    let tH:d.toTypeRuSetup.H:=⟨t,d.toTypeRuSetup.T_le_H ht⟩
    have hm : d.ru2.quotientMap tH∈star (d:=d) d.toTypeRuSetup.R₁ :=
      (star_mono hSR) (h (mem_map.mpr ⟨tH,ht,rfl⟩))
    change tH∈((d.toTypeRuSetup.R₁.subgroupOf d.toTypeRuSetup.H).map
      d.ru2.quotientMap).comap d.ru2.quotientMap at hm
    rw [comap_map_eq_self] at hm
    · exact hm
    · rw [d.ru2.quotient_kernel]
      exact fun _ hx=>hQR hx
  have hcR : Nat.card d.toTypeRuSetup.R₁=8192 := by
    have hh:=(d.toTypeRuSetup.S.subgroupOf d.toTypeRuSetup.R₁).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv,d.ru1.card_S] at hh
    change 2048*d.toTypeRuSetup.S.relIndex d.toTypeRuSetup.R₁=_ at hh
    rw [Fusion.index_R₁_S] at hh
    exact hh.symm
  have hc:=card_le_of_le hT
  rw [d.toTypeRuSetup.card_T_of_card_Z d.card_Z,hcR] at hc
  omega

private theorem star_A_not_le_S (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ¬star (d:=d) (p.A B5)≤star (d:=d) d.toTypeRuSetup.S := by
  intro h
  apply star_S_not_top B5
  rw [←s.A_sup_Q₅_sup_S p B5 hi,
    star_sup _ _ (sup_le (p.A_le_H B5) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _))) d.S_le_H,
    star_sup _ _ (p.A_le_H B5) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)),star_Q₅, sup_bot_eq]
  exact sup_le h le_rfl

private theorem star_A_le_normalizer (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    star (d:=d) (p.A B5)≤normalizer (B5.map d.ru2.quotientMap:Set S5) := by
  rw [←fiveHyperplaneNormalizer_image d B5]
  exact map_mono (fun _ hx=>s.A_normalizes_fiveHyperplane p B5 hi hx)

private theorem starPoint_le_A (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H) :
    s.starPoint≤star (d:=d) (p.A B5) := by
  rw [s.starPoint_eq_image]
  apply star_mono
  exact (s.Uα_le_W₀.trans p.W₀_le_W).trans (p.W_eq_S₂ ▸ p.S₂_le_A B5)

private theorem starPoint_le_S (s:SourceChoice p) : s.starPoint≤star (d:=d) d.toTypeRuSetup.S := by
  rw [s.starPoint_eq_image]
  exact star_mono ((s.Uα_le_W₀.trans p.W₀_le_W).trans p.W_le_S)

private theorem star_A_card (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : Nat.card (star (d:=d) (p.A B5))=4 := by
  let P:=B5.mapSurjective d.ru2.quotient_surjective
  have hd20 : Nat.card (star (d:=d) (p.A B5))∣20 := by
    have h:=card_dvd_of_le (star_A_le_normalizer p s B5 hi)
    exact h.trans (dvd_of_eq (Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.card_normalizer P))
  have hd2048 : Nat.card (star (d:=d) (p.A B5))∣2048 := by
    have h:=(p.A B5).subgroupOf d.toTypeRuSetup.H |>.card_map_dvd d.ru2.quotientMap
    rw [Nat.card_congr (subgroupOfEquivOfLe (p.A_le_H B5)).toEquiv,s.card_A p B5 hi] at h
    exact h
  have hd4 : Nat.card (star (d:=d) (p.A B5))∣4 := Nat.dvd_gcd hd20 hd2048
  have hlt : 2<Nat.card (star (d:=d) (p.A B5)) := by
    apply lt_of_not_ge
    intro hc
    have he:=eq_of_le_of_card_ge (starPoint_le_A p s B5)
      (by rw [s.starPoint_card];exact hc)
    exact star_A_not_le_S p s B5 hi (he ▸ starPoint_le_S p s)
  have hd:=Nat.mem_divisors.mpr ⟨hd4,(by decide:4≠0)⟩
  have he : Nat.divisors 4={1,2,4} := by decide
  simp only [he,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with h | h | h <;> omega

theorem SourceChoice.F₁_image (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ((p.F₁ B5).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap=
      normalizer (B5.map d.ru2.quotientMap:Set S5) := by
  let P:=B5.mapSurjective d.ru2.quotient_surjective
  have he : star (d:=d) (p.F₁ B5)=star (d:=d) (p.A B5)⊔B5.map d.ru2.quotientMap := by
    rw [Plane.F₁,star_sup _ _ (sup_le (p.A_le_H B5) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)))
      (map_subtype_le _),star_sup _ _ (p.A_le_H B5) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)),
      star_Q₅,sup_bot_eq,star_B5]
  change star (d:=d) (p.F₁ B5)=_
  rw [he]
  have hA:=star_A_le_normalizer p s B5 hi
  apply eq_of_le_of_card_ge (sup_le hA (B5.map d.ru2.quotientMap).le_normalizer)
  have hN : Nat.card (normalizer (B5.map d.ru2.quotientMap:Set S5))=20 :=
    Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.card_normalizer P
  have hP : Nat.card (B5.map d.ru2.quotientMap)=5 :=
    Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.card_sylow P
  rw [hN,sup_comm,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _ hA
      (disjoint_of_coprime_natCard (by
        rw [star_A_card p s B5 hi,hP]
        decide)),star_A_card p s B5 hi,
    hP]

end CFSG.Quasithin.ChapterJ.RuSubgroup
