module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.Configuration

/-!
# Conditional assembly of the binary distance-four quotient

A shortest critical path supplies the source midpoint. A marked one-factor
quotient is impossible by the actual square-map calculation. In the other
branch the two geometric factors assemble into a surjective homomorphism
with kernel U_alpha and the required contragredient action.

The two branch producers remain explicit premises. This reduction is not
yet the unconditional constructor from LocalSource, Geometry, CommonFacts,
b = 4 and RadiusFacts. Those premises must be discharged by the source
proofs of MS93 (1993), (4.6.11)--(4.6.12), printed pp.909--912.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
variable {M : Type*} [Group M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

theorem doubleDualQuotient_of_local_branches [Finite M]
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (hsmall : ∀ s : CriticalSegment geometry, s.SmallIntersection →
      Nonempty (SingleQuotient source common (fun g v => g.val.mulVec v)) ∨
        Nonempty (SingleQuotient source common Linear.dual))
    (hlarge : ∀ s : CriticalSegment geometry, ¬ s.SmallIntersection →
      Nonempty (OrbitFactors source common s.middle)) :
    Nonempty (DoubleDualQuotient source common) := by
  classical
  obtain ⟨s⟩ := exists_criticalSegment geometry hb
  by_cases hs : s.SmallIntersection
  · rcases hsmall s hs with h | h
    · obtain ⟨d⟩ := h
      exact (d.natural_impossible radius).elim
    · obtain ⟨d⟩ := h
      exact (SingleQuotient.dual_impossible radius d).elim
  · obtain ⟨f⟩ := hlarge s hs
    exact doubleDualQuotient_of_factors source common radius f.left f.right
      f.left_data f.right_data f.generate f.intersect

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
