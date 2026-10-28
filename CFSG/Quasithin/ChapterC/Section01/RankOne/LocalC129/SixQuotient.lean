module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiSieve
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiZeroRank
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PPerfectHom

/-!
# No χ-block in an A₆ or S₆ two-core extension

A χ₀ block has three-rank at most one, while A₆ has three-rank two.
The sole remaining strongly quasithin χ type, ordinary A₇, has a different
quotient order. Subnormality makes a nontrivial block image in A₆ the whole
simple group; two-perfection puts every block image in S₆ inside A₆.
These are the six-point-stabilizer exclusions in C.1.29, printed p.134.
-/
public section
namespace CFSG.Quasithin.ChapterC.LocalC129
open Subgroup Theory.GroupTheory
variable {G L : Type*} [Group G] [Finite G] [Group L] [Finite L]

theorem not_chi_of_six_quotient (hs : IsStronglyQuasithin L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) : ¬ IsChiBlock L := by
  intro h
  rcases chi_zero_or_alternating_seven hs h with h | h
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    have he : primeRank 3 L = 2 := by
      rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 L)
        pCore_isPGroup, primeRank_congr 3 e,
        GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)]
    have hr := h.threeRank_le_one
    omega
  · obtain ⟨e7⟩ := h.2.2.quotient_iso
    have hc := Nat.card_congr (e.symm.trans e7).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
    norm_num at hc

theorem no_chiBlock_of_six_core_quotient
    (hs : IsStronglyQuasithin G)
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 6))
    (K : Subgroup G) : ¬ IsChiBlockIn K := by
  intro h
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (G ⧸ pCore 2 G) := e.isSimpleGroup
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := q.subgroupMap K
  have hker : f.ker = pCore 2 K := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 h.1.subnormal).symm
  let eK : K ⧸ pCore 2 K ≃* K.map q :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective K))
  rcases (h.1.subnormal.map (QuotientGroup.mk'_surjective (pCore 2 G))).eq_bot_or_top_of_isSimpleGroup
      inferInstance with hz | ht
  · have hle : K ≤ pCore 2 G := by
      simpa only [QuotientGroup.ker_mk'] using (map_eq_bot_iff K).mp hz
    have hp : IsPGroup 2 K := pCore_isPGroup.to_le hle
    have hid := h.1.short.twoPerfect.hom_eq_one_of_isPGroup hp (MonoidHom.id K)
    apply h.1.short.blockU_ne_bot
    apply eq_bot_iff.mpr
    intro x _
    exact mem_bot.mpr (DFunLike.congr_fun hid x)
  · let eAll := (MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv
    exact not_chi_of_six_quotient (hs.subgroup K) ((eK.trans eAll).trans e) h.2
theorem no_chiBlock_of_symmetric_six_core_quotient
    (hs : IsStronglyQuasithin G)
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 6))
    (K : Subgroup G) : ¬ IsChiBlockIn K := by
  intro h
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkq : q.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let f := q.subgroupMap K
  have hker : f.ker = pCore 2 K := by
    rw [ker_subgroupMap, hkq]
    exact (pCore_subnormal_eq_comap 2 h.1.subnormal).symm
  let eK : K ⧸ pCore 2 K ≃* K.map q :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective K))
  have hu : IsPGroup 2 ℤˣ := IsPGroup.of_card (n := 1) (by
    simp [Nat.card_eq_fintype_card, Fintype.card_units_int])
  have hsign := h.1.short.twoPerfect.hom_eq_one_of_isPGroup hu
    (Equiv.Perm.sign.comp (q.comp K.subtype))
  have hDA : K.map q ≤ alternatingGroup (Fin 6) := by
    rintro a ⟨k, hk, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mpr (DFunLike.congr_fun hsign ⟨k, hk⟩)
  have hsub := (h.1.subnormal.map hq).subgroupOf (K := alternatingGroup (Fin 6))
  rcases hsub.eq_bot_or_top_of_isSimpleGroup inferInstance with hz | ht
  · have he : K.map q = ⊥ := by
      have he := congrArg (Subgroup.map (alternatingGroup (Fin 6)).subtype) hz
      simpa only [map_subgroupOf_eq_of_le hDA, Subgroup.map_bot] using he
    have hle : K ≤ pCore 2 G := by rw [← hkq]; exact (map_eq_bot_iff K).mp he
    have hp : IsPGroup 2 K := pCore_isPGroup.to_le hle
    have hid := h.1.short.twoPerfect.hom_eq_one_of_isPGroup hp (MonoidHom.id K)
    apply h.1.short.blockU_ne_bot
    apply eq_bot_iff.mpr
    intro x _
    exact mem_bot.mpr (DFunLike.congr_fun hid x)
  · let eA := (subgroupOfEquivOfLe hDA).symm.trans
      ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv)
    exact not_chi_of_six_quotient (hs.subgroup K) (eK.trans eA) h.2
end CFSG.Quasithin.ChapterC.LocalC129
