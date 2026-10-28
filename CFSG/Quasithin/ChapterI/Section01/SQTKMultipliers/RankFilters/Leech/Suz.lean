module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.RankFilters.Leech.KernelReduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.TwoKernel

/-!
# Suz is excluded from the simple strongly quasithin list

The fixed ATLAS carrier has an elementary abelian three-subgroup of order 27
inside the explicitly constructed involution centralizer. This gives local
three-rank at least three and contradicts quasithinness. It independently
supplies the direct-embedding alternative to the conditional two-kernel route;
no assertion about the full orthogonal quotient or a splitting is needed.

This discharges the Suz exclusion used in Aschbacher--Smith A.2.19 and I.1.3,
printed pp.40--41 and 407, for every group actually isomorphic to the carrier.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech

/-- The fixed sporadic Suz carrier is not quasithin. -/
theorem suz_not_quasithin : ¬ IsQuasithin _root_.Sporadic.LeechRelated.Suz.Carrier := by
  intro h
  have hr := _root_.Sporadic.LeechRelated.Suz.CentralizerSection.numerator_primeRank_three_ge
  have hc := primeRank_mono 3
    _root_.Sporadic.LeechRelated.Suz.CentralizerSection.numerator_centralizes
  have hl := (Theory.GroupTheory.isTwoLocal_involution_centralizer
    _root_.Sporadic.LeechRelated.Suz.CentralizerSection.involution_order).primeRank_le 3
  have hu := isQuasithin_iff_twoLocalPrimeRank.mp h 3 (by decide) (by decide)
  have := ((hr.trans hc).trans hl).trans hu
  omega

variable {G : Type*} [Group G] [Finite G]

/-- The Suz obstruction transports through an actual carrier isomorphism. -/
theorem suz_not_quasithin_of_equiv
    (e : G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier) : ¬ IsQuasithin G :=
  fun h => suz_not_quasithin (Theory.GroupTheory.isQuasithin_of_equiv e h)

/-- The unconditional Suz exclusion needed by the simple SQTK multiplier filter. -/
theorem suz_not_stronglyQuasithin_of_equiv
    (e : G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier) : ¬ IsStronglyQuasithin G :=
  fun h => suz_not_quasithin_of_equiv e h.quasithin

end CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech
