module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.RankFilters.Leech.KernelReduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co2.CentralizerSection.TwoKernel

/-!
# The unconditional Co₂ local-rank exclusion

Three checked commuting cubic words embed E₂₇ into the actual centralizing-word
subgroup of the fixed degree-2300 ATLAS carrier. Its containment in the centralizer
of the existing involution puts this rank in a genuine two-local subgroup.
Thus Co₂ is not quasithin, and every finite group actually isomorphic to this
carrier fails strong quasithinness.

This uses the direct elementary-subgroup alternative to the conditional
kernel-lifting route in `KernelReduction`; no two-group assertion about the
symplectic action kernel is assumed or inferred from the coloring.

Source: Aschbacher–Smith A.2.19 and I.1.3, printed pp.40–41 and 407;
GLS3 Table 5.3k, the 2A involution centralizer.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech

/-- An actual elementary abelian subgroup contributes three-rank to a Co₂ two-local. -/
theorem co2_three_le_twoLocalPrimeRank :
    3 ≤ twoLocalPrimeRank 3 _root_.Sporadic.LeechRelated.Co2.Carrier := by
  have hr := _root_.Sporadic.LeechRelated.Co2.CentralizerSection.ThreeRank.three_le_primeRank_numerator
  have hc := _root_.Sporadic.LeechRelated.Co2.CentralizerSection.numerator_centralizes
  have ht := Theory.GroupTheory.isTwoLocal_involution_centralizer
    _root_.Sporadic.LeechRelated.Co2.CentralizerSection.z_order
  exact (hr.trans (primeRank_mono 3 hc)).trans (ht.primeRank_le 3)

/-- The fixed Co₂ carrier violates the odd-rank bound in an involution centralizer. -/
theorem co2_not_quasithin : ¬ IsQuasithin _root_.Sporadic.LeechRelated.Co2.Carrier := by
  intro h
  have hb := isQuasithin_iff_twoLocalPrimeRank.mp h 3 (by decide) (by decide)
  have hr := co2_three_le_twoLocalPrimeRank
  omega

/-- In particular the concrete Co₂ model is not strongly quasithin. -/
theorem co2_not_stronglyQuasithin :
    ¬ IsStronglyQuasithin _root_.Sporadic.LeechRelated.Co2.Carrier :=
  fun h => co2_not_quasithin h.quasithin

variable {G : Type*} [Group G] [Finite G]

/-- The local-rank obstruction transports through an actual model isomorphism. -/
theorem co2_not_quasithin_of_equiv
    (e : G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) : ¬ IsQuasithin G :=
  fun h => co2_not_quasithin (Theory.GroupTheory.isQuasithin_of_equiv e h)

/-- The unconditional Co₂ exclusion required by the I.1.3 SQTK rank filter. -/
theorem co2_not_stronglyQuasithin_of_equiv
    (e : G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) : ¬ IsStronglyQuasithin G :=
  fun h => co2_not_quasithin_of_equiv e h.quasithin

end CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech
