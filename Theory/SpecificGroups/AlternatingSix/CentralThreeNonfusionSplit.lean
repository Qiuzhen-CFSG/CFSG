module
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.PerfectCentralSupplement
public import Theory.GroupTheory.PGroup.OrderTwentySevenMarkedCenter
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCosetFusion
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.Complement

/-!
# Splitting a central cubic cover of A₆ from an actual nonfusion pair

If the full central kernel meets the derived subgroup nontrivially, its
prime order makes the whole extension perfect. Transfer puts that kernel
in the derived subgroup of a Sylow group of order27 containing the actual
cubic. This Sylow is nonabelian, with center equal to the same full kernel.
Extraspecial central-coset fusion then contradicts the prescribed nonfusion.
Thus the actual derived subgroup complements the complete central kernel.

This is the elementary cubic-cover step in Baumeister, Lemma 2.4.
-/

public noncomputable section
open Subgroup
namespace AlternatingSix.CentralThreeNonfusionSplit

/-- One actual nonfusion pair detects splitting of the full central cubic cover. -/
theorem kernel_complement_of_nonfusion
    {E : Type*} [Group E] [Finite E]
    (f : E →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 3)
    (x : E) (hx : orderOf x = 3) (hfx : f x ≠ 1)
    (z : E) (hz : z ∈ f.ker) (hnf : ¬ IsConj x (z*x)) :
    f.ker.IsComplement' (commutator E) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let D := commutator E
  have hmap : D.map f = ⊤ := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf,commutator_eq_self]
  have hgen : f.ker ⊔ D = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨d,hd,hda⟩ := (show f a ∈ D.map f from hmap ▸ mem_top _)
    have ha : a*d⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hda,mul_inv_cancel]
    have hm := mul_mem (mem_sup_left ha) (mem_sup_right hd)
    simpa only [inv_mul_cancel_right] using hm
  have hdis : Disjoint f.ker D := by
    by_contra hnot
    have hcap : Nat.card (f.ker ⊓ D : Subgroup E) = 3 := by
      have hd := card_dvd_of_le (show f.ker ⊓ D ≤ f.ker from inf_le_left)
      rw [hk] at hd
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h | h
      · exact False.elim (hnot (disjoint_iff.mpr (card_eq_one.mp h)))
      · exact h
    have hle : f.ker ≤ D := by
      have he : f.ker ⊓ D = f.ker := eq_of_le_of_card_ge inf_le_left (by rw [hcap,hk])
      exact he ▸ inf_le_right
    have hD : D = ⊤ := by simpa only [sup_eq_right.mpr hle] using hgen
    let : Group.IsPerfect E := ⟨hD⟩
    have hE : Nat.card E = 1080 := by
      have h := f.ker.index_mul_card
      rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,hk,nat_card_alternatingGroup] at h
      norm_num [Nat.factorial] at h
      omega
    have hxp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,hx]; rfl)
    obtain ⟨P,hxP⟩ := hxp.exists_le_sylow
    have hP : Nat.card P = 27 := by
      rw [P.card_eq_multiplicity,hE]
      decide +kernel
    have hkp : IsPGroup 3 f.ker := IsPGroup.of_card (n := 1) (by simpa using hk)
    have hkP : f.ker ≤ P := hkp.le_sylow_of_normal P
    have hkn : f.ker ≤ ⁅(P : Subgroup E),(P : Subgroup E)⁆ :=
      central_pSubgroup_le_commutator (p := 3) (P : Subgroup E) f.ker hkP hc hkp
        (by exact P.not_dvd_index)
    have hn : ¬ IsMulCommutative P := by
      intro hab
      have he : f.ker = ⊥ := le_bot_iff.mp (hkn.trans_eq (commutator_self_eq_bot_iff.mpr hab))
      have hh := card_eq_one.mpr he
      omega
    let : IsExtraspecial 3 P := OrderTwentySeven.extraspecial hP hn
    have hcenter : f.ker.subgroupOf P = center P := by
      apply eq_of_le_of_card_ge
      · intro a ha
        exact mem_center_iff.mpr fun b => Subtype.ext (mem_center_iff.mp (hc ha) b)
      · rw [Nat.card_congr (subgroupOfEquivOfLe hkP).toEquiv,hk,
          OrderTwentySeven.center_card hP hn]
    let xP : P := ⟨x,hxP (mem_zpowers x)⟩
    let zP : P := ⟨z,hkP hz⟩
    have hxc : xP ∉ center P := by
      rw [←hcenter]
      exact hfx
    have hzc : zP ∈ center P := hcenter ▸ hz
    have he : QuotientGroup.mk' (center P) xP = QuotientGroup.mk' (center P) (zP*xP) := by
      have hzq : QuotientGroup.mk' (center P) zP = 1 := (QuotientGroup.eq_one_iff zP).mpr hzc
      rw [map_mul,hzq,one_mul]
    have hconj := IsExtraspecial.isConj_of_center_quotient_eq_prime (p := 3) hxc he
    exact hnf ((P : Subgroup E).subtype.map_isConj hconj)
  apply isComplement'_of_disjoint_and_mul_eq_univ hdis
  rw [←coe_mul_of_left_le_normalizer_right f.ker D le_normalizer_of_normal,hgen,coe_top]

end AlternatingSix.CentralThreeNonfusionSplit
