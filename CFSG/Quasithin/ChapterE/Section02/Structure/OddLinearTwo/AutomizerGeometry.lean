module

public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.SylowCentralFusion.CenterSelection
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Faithfulness and the small-Sylow obstruction for the odd source row

The centralizer of a centerless normal Sylow supplement embeds in the
quotient by that supplement. It is a normal two-group and hence vanishes
when O₂(H)=1. Separately, a fused central involution with a unique maximal
centralizer forces |T|>8: centric fusion selects a normalizer mover, whereas
every subgroup containing that involution is T-normal when |T|≤8.

Source: Aschbacher–Smith E.2.2(2c), printed pp.215–216.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure

private theorem normal_of_small_two_group_of_central_involution
    {P : Type*} [Group P] [Finite P] (hp : IsPGroup 2 P)
    (hcard : Nat.card P ≤ 8) (Q : Subgroup P)
    (t : P) (ht : orderOf t = 2) (htQ : t ∈ Q) (htZ : t ∈ center P) : Q.Normal := by
  have htcard : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  have htQle : zpowers t ≤ Q := zpowers_le.mpr htQ
  by_cases htwo : Nat.card Q = 2
  · have he : Q = zpowers t := (eq_of_le_of_card_ge htQle (by omega)).symm
    have hQC : Q ≤ center P := he ▸ (zpowers_le.mpr htZ)
    refine ⟨?_⟩
    intro q hq g
    have hh := mem_center_iff.mp (hQC hq) g
    simpa only [hh, mul_inv_cancel_right] using hq
  · obtain ⟨n, hn⟩ := (hp.to_subgroup Q).exists_card_eq
    have hfour : 4 ≤ Nat.card Q := by
      have hlow : 2 ≤ Nat.card Q := htcard ▸ card_le_of_le htQle
      have hn0 : n ≠ 0 := by
        intro he
        have hc : Nat.card Q = 1 := by simpa [he] using hn
        omega
      have hn1 : n ≠ 1 := by
        intro he
        apply htwo
        simpa [he] using hn
      have hn2 : 2 ≤ n := by omega
      rw [hn]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hn2
    have hc := Q.card_mul_index
    have hi : Q.index ≤ 2 := by nlinarith
    have hipos : 0 < Q.index := Nat.card_pos
    have hh : Q.index = 1 ∨ Q.index = 2 := by omega
    rcases hh with hh | hh
    · have he := index_eq_one.mp hh
      rw [he]
      infer_instance
    · exact normal_of_index_eq_two hh

/-- A fused central involution cannot have its centralizer as the unique
maximal Sylow overgroup when that Sylow has order at most eight. -/
theorem eight_lt_sylow_card_of_max_centralizer
    {H : Type*} [Group H] [Finite H] (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hO : pCore 2 H = ⊥)
    (t : H) (ht : orderOf t = 2) (htT : t ∈ (T : Subgroup H))
    (htZ : t ∈ centralizer (T : Set H))
    (hM : ChapterB.minimalParabolicMax T hP = centralizer ({t} : Set H))
    (hf : ∃ g : H, g * t * g⁻¹ ∈ (T : Subgroup H) ∧ g * t * g⁻¹ ≠ t) :
    8 < Nat.card T := by
  by_contra! hsmall
  obtain ⟨w, _⟩ := SylowCentralFusion.exists_center_normalizerSelection T t htT hf
  have hwN : (w.subgroup.subgroupOf (T : Subgroup H)).Normal := by
    apply normal_of_small_two_group_of_central_involution T.isPGroup' hsmall _ ⟨t, htT⟩
    · exact (orderOf_injective (T : Subgroup H).subtype Subtype.val_injective ⟨t, htT⟩).symm.trans ht
    · exact w.mem_subgroup
    · apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (htZ a a.property)
  have hTN : (T : Subgroup H) ≤ normalizer (w.subgroup : Set H) :=
    (normal_subgroupOf_iff_le_normalizer w.le_sylow).mp hwN
  have hNne : normalizer (w.subgroup : Set H) ≠ ⊤ := by
    intro he
    have hn := normalizer_eq_top_iff.mp he
    have hpw : IsPGroup 2 w.subgroup := T.isPGroup'.of_injective
      (inclusion w.le_sylow) (inclusion_injective _)
    have hwb : w.subgroup ≤ pCore 2 H := le_sSup ⟨hn, hpw⟩
    have ht1 : t = 1 := by
      have hh := hwb w.mem_subgroup
      rwa [hO, mem_bot] at hh
    simp [ht1] at ht
  have hNM := hP.1.le_maximal
    ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩ hTN
    (lt_top_iff_ne_top.mpr hNne)
  obtain ⟨g, hg, hmove⟩ := w.moves
  have hgC : g ∈ centralizer ({t} : Set H) := hM ▸ hNM hg
  apply hmove
  rw [mem_centralizer_singleton_iff.mp hgC, mul_inv_cancel_right]

/-- The original trivial two-core makes conjugation on K faithful. -/
theorem centralizer_eq_bot_of_centerless_sylow_supplement
    {H : Type*} [Group H] [Finite H] (T : Sylow 2 H)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hZ : center K = ⊥) (hO : pCore 2 H = ⊥) :
    centralizer (K : Set H) = ⊥ := by
  let C := centralizer (K : Set H)
  let q := QuotientGroup.mk' K
  let f := q.comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro c hc
    have hq : q (c : H) = 1 := hc
    have hcK : (c : H) ∈ K := (QuotientGroup.eq_one_iff (c : H)).mp hq
    have hcZ : (⟨c, hcK⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      apply Subtype.ext
      exact c.property k k.property
    have hc1 : (c : H) = 1 := by
      have hh : (⟨c, hcK⟩ : K) = 1 := by simpa only [hZ, mem_bot] using hcZ
      exact congrArg Subtype.val hh
    exact mem_bot.mpr (Subtype.ext hc1)
  have hqP := isPGroup_quotient_of_sup_eq_top K (T : Subgroup H) T.isPGroup' hgen
  have hCP : IsPGroup 2 C := hqP.of_injective f hf
  have hcore : C ≤ pCore 2 H := le_sSup ⟨inferInstance, hCP⟩
  exact le_bot_iff.mp (hcore.trans_eq hO)


end CFSG.Quasithin.ChapterE.Structure
