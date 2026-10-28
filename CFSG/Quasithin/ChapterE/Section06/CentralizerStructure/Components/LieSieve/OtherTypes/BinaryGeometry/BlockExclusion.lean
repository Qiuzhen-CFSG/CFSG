module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.Parabolics
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.BlockExclusion.Transfer
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.BlockExclusion.Intrinsic

/-!
# No chi-zero blocks in the lifted binary parabolic joins

Every relatively subnormal chi-zero block in the lifted join is
two-perfect. It therefore embeds, with its subnormal chain retained,
in the actual binary parabolic. The intrinsic calculation excludes it:
the radical-pair obstruction handles both paired five-dimensional flags,
and the simple GL₃(2) Levi quotient handles the four-dimensional ends.

Only normalization, the two-group supplement, and quotient invariance
are needed here. Consequently the five-dimensional result allows an
outer graph actor. In dimension four the parent's inner-action condition
is used to obtain invariant end parabolics; once that invariance is given,
the block exclusion itself needs no additional action hypothesis.

The source Q is a centralizer in the supplied Sylow two-subgroup, so its
two-group condition follows directly. Neither characteristic two nor the
remaining E.6.1 hypotheses are needed for this exclusion step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248, and C.1.7/C.1.12, printed pp.123–124.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry

variable {G : Type*} [Group G] {Q L : Subgroup G}

/-- Both literal paired flags have block-free lifted joins, even with a graph actor. -/
theorem fivePairedParabolic_noChiZeroBlocks
    (hm : ClassicalGroup.IsPSL L 5 2) (hN : Q ≤ normalizer (L : Set G))
    (hQ : IsPGroup 2 Q) (b : BinaryLinear.FiveFlagGeometry.FiveBasis) (i : Fin 2)
    (hi : sylowImage Q L ≤ normalizer
      (quotientParabolic Q (by decide) hm (fivePairedParabolic b i) : Set _)) :
    NoChiZeroBlocks
      (quotientPreimage Q L (quotientParabolic Q (by decide) hm (fivePairedParabolic b i)) ⊔ Q) := by
  intro B hBD hs hB
  obtain ⟨f, hf, hs⟩ := exists_subnormal_model_embedding (by decide) hm hN hQ
    (fivePairedParabolic b i) hi hBD hs hB.chi.short.twoPerfect
  exact fivePairedParabolic_not_short b i f hf hs hB.chi.short

/-- Either invariant end parabolic in dimension four has a block-free lifted join. -/
theorem fourEndParabolic_noChiZeroBlocks
    (hm : ClassicalGroup.IsPSL L 4 2) (hN : Q ≤ normalizer (L : Set G))
    (hQ : IsPGroup 2 Q) (b : BinaryLinear.InvariantNodeActions.Basis 3) (i : Fin 2)
    (hi : sylowImage Q L ≤ normalizer
      (quotientParabolic Q (by decide) hm (fourEndParabolic b i) : Set _)) :
    NoChiZeroBlocks
      (quotientPreimage Q L (quotientParabolic Q (by decide) hm (fourEndParabolic b i)) ⊔ Q) := by
  intro B hBD hs hB
  obtain ⟨f, hf, hs⟩ := exists_subnormal_model_embedding (by decide) hm hN hQ
    (fourEndParabolic b i) hi hBD hs hB.chi.short.twoPerfect
  exact fourEndParabolic_not_chiZero b i f hf hs hB

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry

end
