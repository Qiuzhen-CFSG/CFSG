module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrdinaryLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreGeometry.Action
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
/-!
# Involutions fixing a Sylow-normalized HS section

A Sylow-normalized elementary subgroup of order at least eight is the
characteristic elementary eight of the marked Sylow subgroup. Its normalizer
is perfect of order 10752. A subgroup normalized by the full Sylow and with
order divisible by 168 must therefore be this entire normalizer. An
involutory automorphism fixing it is inner, and the concrete generation by
this normalizer and the marked involution centralizer makes it trivial.

This uses only the existing literal HS carrier and its checked local geometry.
It supplies the HS comparison in Aschbacher--Smith 10.2.9 (pp.750--751).
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.HS
open EvenLocalCandidates BlockNormalizer BlockNormalizer.CoreGeometry

private theorem normalized_top (B : Subgroup baseNormalizer)
    (hn : ((baseSylow.subtype baseSylow_le_normalizer) : Subgroup baseNormalizer) ≤
      normalizer (B : Set baseNormalizer))
    (h168 : 168 ∣ Nat.card B) : B = ⊤ := by
  let S := baseSylow.subtype baseSylow_le_normalizer
  have hs : Nat.card S = 512 := by
    change Nat.card ((baseSylow : Subgroup Carrier).subgroupOf baseNormalizer) = 512
    rw [Nat.card_congr (subgroupOfEquivOfLe baseSylow_le_normalizer).toEquiv]
    exact subgroup_card
  have hJ : B ⊔ (S : Subgroup baseNormalizer) = ⊤ := by
    apply eq_top_of_card_eq
    apply Nat.dvd_antisymm
    · exact (B ⊔ (S : Subgroup baseNormalizer)).card_subgroup_dvd_card
    · rw [normalizer_card]
      have h1 := h168.trans (card_dvd_of_le (show B ≤ B ⊔ (S : Subgroup _) from le_sup_left))
      have h2 : 512 ∣ Nat.card ↥(B ⊔ (S : Subgroup baseNormalizer)) :=
        hs ▸ card_dvd_of_le (show (S : Subgroup _) ≤ B ⊔ (S : Subgroup _) from le_sup_right)
      simpa only [show Nat.lcm 168 512 = 10752 from by decide] using Nat.lcm_dvd h1 h2
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←hJ]; exact sup_le B.le_normalizer hn))
  have hd : Nat.card (baseNormalizer ⧸ B) ∣ 2^6 := by
    apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 168)
    have hh := Nat.mul_dvd_mul_right h168 (Nat.card (baseNormalizer ⧸ B))
    rw [←index_eq_card,B.card_mul_index,normalizer_card] at hh
    exact hh
  have hp : IsPGroup 2 (baseNormalizer ⧸ B) := isPGroup_iff_card_dvd_pow.mpr ⟨6,hd⟩
  let : Group.IsNilpotent (baseNormalizer ⧸ B) := hp.isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ B)

private theorem fixed_base_normalizer (B E : Subgroup Carrier)
    (hSB : (baseSylow : Subgroup Carrier) ≤ normalizer (B : Set Carrier))
    (hSE : (baseSylow : Subgroup Carrier) ≤ normalizer (E : Set Carrier))
    (hBE : B ≤ normalizer (E : Set Carrier))
    (hE : IsElementaryAbelian 2 E) (hc : 8 ≤ Nat.card E)
    (h168 : 168 ∣ Nat.card B) : B = baseNormalizer := by
  let := hE
  have hES : E ≤ (baseSylow : Subgroup Carrier) := by
    have hh := baseSylow.is_maximal' (baseSylow.isPGroup'.to_sup_of_normal_right'
      (IsElementaryAbelian.isPGroup 2 E) hSE) le_sup_left
    exact hh ▸ le_sup_right
  let R := E.subgroupOf (baseSylow : Subgroup Carrier)
  have hR : R ≠ ⊥ := by
    intro hz
    have hh : E = ⊥ := by
      rw [←map_subgroupOf_eq_of_le hES]
      change R.map (baseSylow : Subgroup Carrier).subtype = ⊥
      rw [hz,Subgroup.map_bot]
    rw [hh,card_bot] at hc
    omega
  have hRn : R.Normal := (normal_subgroupOf_iff_le_normalizer hES).mpr hSE
  have hRe : IsElementaryAbelian 2 R := IsElementaryAbelian.subgroupOf hES
  obtain ⟨i,hi⟩ := normal_elementary_catalogue R hR hRn hRe
  have hEi : E = elementary i := (map_subgroupOf_eq_of_le hES).symm.trans hi
  have hEbase : E ≤ baseElementary := by
    rw [hEi]
    apply Subgroup.closure_mono
    rintro x ⟨j,hj,rfl⟩
    exact ⟨j,Fin.le_last j,rfl⟩
  have hEeq : E = baseElementary := eq_of_le_of_card_ge hEbase (by rw [baseElementary_card]; exact hc)
  have hBN : B ≤ baseNormalizer := by simpa only [hEeq,baseNormalizer,localGroup,baseElementary] using hBE
  have hn : ((baseSylow.subtype baseSylow_le_normalizer) : Subgroup baseNormalizer) ≤
      normalizer (B.subgroupOf baseNormalizer : Set baseNormalizer) := by
    rw [←subgroupOf_normalizer_eq hBN]
    exact comap_mono hSB
  have htop := normalized_top (B.subgroupOf baseNormalizer) hn
    (Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv ▸ h168)
  exact le_antisymm hBN (subgroupOf_eq_top.mp htop)

theorem eq_one_of_fixes_normalized_large_section
    (S : Sylow 2 Carrier) (B E : Subgroup Carrier)
    (hSB : (S : Subgroup Carrier) ≤ normalizer (B : Set Carrier))
    (hSE : (S : Subgroup Carrier) ≤ normalizer (E : Set Carrier))
    (hBE : B ≤ normalizer (E : Set Carrier))
    (hE : IsElementaryAbelian 2 E) (hc : 8 ≤ Nat.card E)
    (h168 : 168 ∣ Nat.card B)
    (a : MulAut Carrier) (ha : a^2=1) (hf : ∀ x ∈ B, a x = x) : a=1 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S baseSylow
  let d := MulAut.conj g
  have hS : (S : Subgroup Carrier).map d.toMonoidHom = (baseSylow : Subgroup Carrier) :=
    congrArg Sylow.toSubgroup hg
  let B' := B.map d.toMonoidHom
  let E' := E.map d.toMonoidHom
  have hB : B' = baseNormalizer := fixed_base_normalizer B' E' (by
      rw [←hS]
      exact (map_mono hSB).trans (le_normalizer_map _)) (by
      rw [←hS]
      exact (map_mono hSE).trans (le_normalizer_map _))
    ((map_mono hBE).trans (le_normalizer_map _))
    (by let := hE; exact IsElementaryAbelian.map _)
    (by rwa [card_map_of_injective d.injective])
    (by rwa [card_map_of_injective d.injective])
  let b := MulAut.congr d a
  have hbfix : ∀ x ∈ baseNormalizer, b x=x := by
    intro x hx
    rw [←hB] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    change d (a (d.symm (d y))) = d y
    rw [d.symm_apply_apply,hf y hy]
  have hbS : ∀ x ∈ baseSylow, b x=x := fun x hx => hbfix x (baseSylow_le_normalizer hx)
  by_contra hne
  have hb2 : b^2=1 := by rw [←map_pow,ha,map_one]
  have hbne : b ≠ 1 := fun h => hne ((MulAut.congr d).injective (h.trans (map_one _).symm))
  obtain ⟨y,hy⟩ := OrdinaryLocal.automorphism_inner_of_fixes_sylow baseSylow b hbS
  have hb := base_inner_eq_conj_e0 b (orderOf_eq_prime_iff.mpr ⟨hb2,hbne⟩)
    ⟨y,hy.symm⟩ hbS
  have hcent : baseNormalizer ≤ centralizer ({e0} : Set Carrier) := by
    intro x hx
    have hh := hbfix x hx
    rw [hb,MulAut.conj_apply] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
  have htop : centralizer ({e0} : Set Carrier) = ⊤ := by
    rw [← centralizer_sup_baseNormalizer_eq_top]
    exact (sup_eq_left.mpr hcent).symm
  have he0 : e0 ∈ center Carrier := by
    apply mem_center_iff.mpr
    intro x
    exact mem_centralizer_singleton_iff.mp (htop ▸ mem_top x)
  rw [center_carrier_eq_bot,mem_bot] at he0
  have hb1 : b=1 := by rw [hb,he0,map_one]
  exact hbne hb1
end Sporadic.LeechRelated.HS
