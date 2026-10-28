module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.RankFilters.Leech.KernelReduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.TwoKernel

/-!
# The concrete Co₁ exclusion from simple SQTK

The fixed ATLAS carrier contains an actual C₃³ in the displayed numerator
of its involution centralizer. This directly contradicts the odd-rank bound
on two-local subgroups. It discharges the Co₁ exclusion by the permitted
elementary-embedding route; the older conditional action-kernel reductions
remain available with their original statements.

Source: Aschbacher--Smith A.2.19 and I.1.3, printed pp.40--41 and 407;
GLS3 Table 5.3l. All transport uses an actual multiplicative equivalence to
the fixed matrix carrier.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech

/-- The explicit rank-three subgroup lies in an actual involution centralizer. -/
theorem co1_not_quasithin : ¬ IsQuasithin _root_.Sporadic.LeechRelated.Co1.Carrier := by
  intro h
  let C := Subgroup.centralizer
    ({_root_.Sporadic.LeechRelated.Co1.CentralizerSection.z} :
      Set _root_.Sporadic.LeechRelated.Co1.Carrier)
  have hC : IsStronglyQuasithin C := isQuasithin_iff_twoLocal.mp h C
    (Theory.GroupTheory.isTwoLocal_involution_centralizer
      _root_.Sporadic.LeechRelated.Co1.CentralizerSection.z_order)
  have hr := Theory.GroupTheory.primeRank_le_of_injective 3
    (Subgroup.inclusion _root_.Sporadic.LeechRelated.Co1.CentralizerSection.numerator_centralizes)
    (Subgroup.inclusion_injective _)
  have hlarge :=
    _root_.Sporadic.LeechRelated.Co1.CentralizerSection.ElementaryThree.numerator_primeRank_three_ge
  have hsmall := hC 3 (by decide) (by decide)
  exact (by decide : ¬ (3 ≤ 2)) (hlarge.trans (hr.trans hsmall))

/-- Any finite group actually isomorphic to the fixed Co₁ carrier fails SQTK's rank bound. -/
theorem co1_not_stronglyQuasithin_of_equiv {G : Type*} [Group G] [Finite G]
    (e : G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) : ¬ IsStronglyQuasithin G :=
  fun h => co1_not_quasithin (Theory.GroupTheory.isQuasithin_of_equiv e h.quasithin)

end CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech
