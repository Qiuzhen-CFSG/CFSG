module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.LocalSeries
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SimpleQuotient
public import Theory.GroupTheory.SimpleSubnormalSeries

/-!
# Excluding subnormal chi-zero blocks in the Rudvalis local series

A chi-zero block B has an actual simple quotient B/O₂(B). Subnormal section
transfer along the supplied relative normal series forces this quotient to
occur in one of its factors. A two-group factor is excluded by the block's
two-perfectness. In either remaining simple factor, the subnormal image is
trivial or the whole factor, so its nontrivial simple quotient has order
168 or 6048. The established chi-zero order obstructions exclude both.

`LocalGeometry.centralizerBlockCover` discharges the series premise of the
existing cover constructor. Construction of the actual Rudvalis local
geometry remains with the Rudvalis assembly owner.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526, and the local-series
contract based on GLS3 Table 5.3r. No normality in the whole ambient group
is substituted for normality relative to the next series term.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase
open Subgroup ChapterC Theory.GroupTheory
variable {K : Type*} [Group K]

/-- A group with the specified local factor series has no subnormal chi-zero
block. The quotient used throughout is `B / O₂(B)`. -/
theorem LocalFactorSeries.not_chiZeroBlockIn
    (c : LocalFactorSeries K) (B : Subgroup K) : ¬ IsChiZeroBlockIn B := by
  intro hB
  let Q := B ⧸ pCore 2 B
  let : IsSimpleGroup Q := hB.2.simple_quotient
  let q : B →* Q := QuotientGroup.mk' (pCore 2 B)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hnot : ¬ IsPGroup 2 Q := by
    intro hp
    have he := (hB.1.short.twoPerfect.of_surjective q hq) ⊥ inferInstance
      (hp.to_quotient ⊥)
    exact bot_ne_top he
  apply no_simple_subnormal_quotient_of_series c.term c.first c.last c.ascending c.normal
      (T := Q) ?_ B hB.1.subnormal q hq
  intro i
  dsimp only
  let := c.normal i
  intro U hU f hf
  rcases c.factor i with hp | ⟨hs, hc⟩
  · exact hnot ((hp.to_subgroup U).of_surjective f hf)
  · let := hs
    rcases hU.eq_bot_or_top_of_isSimpleGroup hs with hb | ht
    · have : Subsingleton U := by rw [hb]; infer_instance
      have : Subsingleton Q := hf.subsingleton
      exact not_subsingleton Q inferInstance
    · subst U
      let : IsSimpleGroup (⊤ : Subgroup
          (c.term i.succ ⧸ (c.term i.castSucc).subgroupOf (c.term i.succ))) :=
        Subgroup.topEquiv.isSimpleGroup
      have hinj : Function.Injective f := by
        apply (MonoidHom.ker_eq_bot_iff f).mp
        rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hk | hk
        · exact hk
        · obtain ⟨y, hy⟩ := exists_ne (1 : Q)
          obtain ⟨x, rfl⟩ := hf y
          exact (hy (MonoidHom.mem_ker.mp (hk ▸ mem_top x))).elim
      have he : Nat.card Q = Nat.card
          (c.term i.succ ⧸ (c.term i.castSucc).subgroupOf (c.term i.succ)) :=
        (Nat.card_congr (MulEquiv.ofBijective f ⟨hinj, hf⟩).toEquiv).symm.trans
          (Nat.card_congr Subgroup.topEquiv.toEquiv)
      rcases hc with hc | hc
      · exact LieType.not_chiZero_of_quotient_card_168 (he.trans hc) hB.2
      · exact not_chiZero_of_quotient_card_6048 (he.trans hc) hB.2

/-- The local geometry now supplies the cover without a separate series premise. -/
def LocalGeometry.centralizerBlockCover {G : Type*} [Group G]
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G} (h : LocalSetup H L M S z)
    {d : SporadicQuotientInput L z .ru}
    (c : LocalGeometry L ((S : Subgroup H).map H.subtype) d) :
    CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z := by
  let := h.finite
  apply c.toCentralizerBlockCover h
  intro K hc B hB
  obtain ⟨s⟩ := hc
  exact s.not_chiZeroBlockIn B hB

end CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase

end
