module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.CubicCentralizers
public import Theory.GroupTheory.NormalizingSubgroupCard
public import Theory.ElementaryAbelian.Basic
public import Theory.PGroupCore

/-!
# A self-centralizing four in an index-fifteen symmetric subgroup

The conjugation image has order six. Cubic centralizers of order nine
exclude a factor three in the ambient four-centralizer. The only remaining
possible enlargement has order twenty; its characteristic five-core would
then be centralized by a cubic in the symmetric subgroup, again impossible.
This is the normalizer step in Aschbacher, *Sporadic Groups* (1994),
Exercise 2(1), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {G:Type*} [Group G] [Finite G]

private theorem normalizer_order (H E:Subgroup G) [IsKleinFour E]
    (hH:Nat.card H=24) (hHN:H≤normalizer (E:Set G))
    (hHC:H⊓centralizer (E:Set G)=E) :
    Nat.card (normalizer (E:Set G))=6*Nat.card (centralizer (E:Set G)) := by
  let f:=E.normalizerMonoidHom
  let fH:=f.comp (inclusion hHN)
  have hk:fH.ker=(H⊓centralizer (E:Set G)).subgroupOf H := by
    ext x
    change f ⟨x,hHN x.property⟩=1 ↔ _
    rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker]
    change (x:G)∈centralizer (E:Set G) ↔ (x:G)∈H ∧ (x:G)∈centralizer (E:Set G)
    simp only [x.property,true_and]
  have hk4:Nat.card fH.ker=4 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,hHC]
    exact IsKleinFour.card_four (G := E)
  have hfr:Nat.card fH.range=6 := by
    have hh:=fH.ker.card_mul_index
    rw [index_ker,hk4,hH] at hh
    omega
  have hrange:fH.range=⊤ := eq_top_of_card_eq fH.range (by rw [hfr,IsKleinFour.card_mulAut E])
  have hr:f.range=⊤ := by
    apply top_unique
    rw [←hrange]
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x,hHN x.property⟩,rfl⟩
  have hh:=f.ker.card_mul_index
  rw [index_ker,hr,Nat.card_congr (topEquiv (G:=MulAut E)).toEquiv,IsKleinFour.card_mulAut E,
    normalizerMonoidHom_ker,Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (E:Set G))).toEquiv] at hh
  omega

private theorem centralizer_three_free (E:Subgroup G) (hE:Nat.card E=4)
    (hc:∀x:G,orderOf x=3 → Nat.card (centralizer ({x}:Set G))=9) :
    ¬3∣Nat.card (centralizer (E:Set G)) := by
  intro hd
  let : Fact (Nat.Prime 3):=⟨by decide⟩
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=centralizer (E:Set G)) 3 hd
  have hxG:orderOf (x:G)=3 := (orderOf_injective (centralizer (E:Set G)).subtype Subtype.val_injective x).trans hx
  have he:E≤centralizer ({(x:G)}:Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (x.property y hy)
  have hh:=card_dvd_of_le he
  rw [hE,hc _ hxG] at hh
  norm_num at hh

private theorem five_core_card_of_twenty {C:Type*} [Group C] [Finite C]
    (hC:Nat.card C=20) : Nat.card (pCore 5 C)=5 := by
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  let S:Sylow 5 C:=Classical.choice inferInstance
  have hS:Nat.card S=5 := by rw [S.card_eq_multiplicity,hC]; decide +kernel
  have hi:(S:Subgroup C).index=4 := by
    have hh:=(S:Subgroup C).card_mul_index
    rw [hS,hC] at hh
    omega
  have hc:Nat.card (Sylow 5 C)=1 := by
    have hd:=S.card_dvd_index
    rw [hi] at hd
    have hm:=card_sylow_modEq_one 5 C
    have hb:=Nat.le_of_dvd (by decide : 0<4) hd
    change Nat.card (Sylow 5 C)%5=1%5 at hm
    omega
  let : Subsingleton (Sylow 5 C):=(Nat.card_eq_one_iff_unique.mp hc).1
  let : (S:Subgroup C).Normal:=S.normal_of_subsingleton
  have hle:(S:Subgroup C)≤pCore 5 C:=le_sSup ⟨inferInstance,S.isPGroup'⟩
  have he:(S:Subgroup C)=pCore 5 C:=(S.is_maximal' pCore_isPGroup hle).symm
  rw [←he,hS]

theorem normalizer_four_eq (H E:Subgroup G) [IsKleinFour E]
    (hG:Nat.card G=360) (hH:Nat.card H=24)
    (hHN:H≤normalizer (E:Set G)) (hHC:H⊓centralizer (E:Set G)=E)
    (hc:∀x:G,orderOf x=3 → Nat.card (centralizer ({x}:Set G))=9) :
    normalizer (E:Set G)=H := by
  let : IsMulCommutative E := IsKleinFour.isMulCommutative
  let C:=centralizer (E:Set G)
  have hE:Nat.card E=4:=IsKleinFour.card_four (G := E)
  have hN:=normalizer_order H E hH hHN hHC
  have h3:¬3∣Nat.card C:=centralizer_three_free E hE hc
  have hdiv:6*Nat.card C∣360 := by
    rw [←hG,←hN]
    exact (normalizer (E:Set G)).card_subgroup_dvd_card
  have h4:4∣Nat.card C := hE ▸ card_dvd_of_le (le_centralizer (H:=E))
  have hcases:Nat.card C=4 ∨ Nat.card C=20 := by
    have hd:Nat.card C∣60 := by
      have hh:6*Nat.card C∣6*60:=hdiv
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0<6)).mp hh
    have hm:=Nat.mem_divisors.mpr ⟨hd,(by decide : 60≠0)⟩
    rw [show Nat.divisors 60={1,2,3,4,5,6,10,12,15,20,30,60} by decide] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with h|h|h|h|h|h|h|h|h|h|h|h <;> simp_all
  rcases hcases with hC4|hC20
  · apply (eq_of_le_of_card_ge hHN ?_).symm
    rw [hH,hN,hC4]
  let D:Subgroup G:=(pCore 5 C).map C.subtype
  have hD:Nat.card D=5 := by
    rw [card_map_of_injective C.subtype_injective]
    exact five_core_card_of_twenty hC20
  have hHD:H≤normalizer (D:Set G) := hHN.trans
    ((normalizer_le_normalizer_centralizer E).trans
      (normalizer_le_normalizer_characteristic_image C (pCore 5 C)))
  let : Fact (Nat.Prime 3):=⟨by decide⟩
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=H) 3 (by rw [hH]; decide)
  have hxG:orderOf (x:G)=3:=(orderOf_injective H.subtype H.subtype_injective x).trans hx
  let α:=D.normalizerMonoidHom ⟨x,hHD x.property⟩
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  let : IsCyclic D:=isCyclic_of_prime_card hD
  have hα4:orderOf α∣4 := by
    have hh:=orderOf_dvd_natCard α
    rw [IsCyclic.card_mulAut,hD] at hh
    exact hh
  have hα3:orderOf α∣3 := by
    have hh:=orderOf_map_dvd D.normalizerMonoidHom (⟨x,hHD x.property⟩:normalizer (D:Set G))
    have ho:orderOf (⟨(x:G),hHD x.property⟩:normalizer (D:Set G))=3 :=
      (orderOf_injective (normalizer (D:Set G)).subtype Subtype.val_injective _).symm.trans hxG
    rwa [ho] at hh
  have hα:α=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 4) hα3 hα4)
  have hxC:(x:G)∈centralizer (D:Set G) := by
    change (⟨x,hHD x.property⟩:normalizer (D:Set G))∈D.normalizerMonoidHom.ker at hα
    rwa [normalizerMonoidHom_ker] at hα
  have hDC:D≤centralizer ({(x:G)}:Set G) := by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr (hxC d hd)
  have hh:=card_dvd_of_le hDC
  rw [hD,hc _ hxG] at hh
  norm_num at hh
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
