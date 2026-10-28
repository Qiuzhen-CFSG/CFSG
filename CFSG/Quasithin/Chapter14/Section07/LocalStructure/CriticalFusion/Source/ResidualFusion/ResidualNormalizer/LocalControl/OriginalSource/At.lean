module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Baumann

/-!
# The earlier 14.7.10 contract at the original ambient Sylow

The natural-point Baumann argument proves the chief-factor or normalizer
alternative from the structural predecessor at the same G,T. Package that
proved implication for all original L,V and flags at this fixed Sylow.
The universal Earlier14710 contract and its producer remain unchanged.

Source: Aschbacher--Smith C.1.37, pp.141--143, and 14.7.10, p.1045.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
namespace ResidualNormalizer.LocalControl
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original 14.7.10 alternative for all natural flags at this G,T.
Its argument order agrees with the universal contract after fixing G,T. -/
@[expose] def Earlier14710At (T : Sylow 2 G) : Prop :=
  ∀ (L V : Subgroup G) (F : InvariantFlag T V 3),
    Counterexample T L → HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 →
    IsMulCommutative F.U →
      (∀ s : NoncentralChiefRefinement.ChiefSeries (F.Li L 1),
        s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 3) ∨
      normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G)

namespace OriginalSource

/-- The actual natural-point MS theorem supplies the localized source
contract using only the structural predecessor at the same ambient Sylow. -/
theorem earlier14710At_of_naturalPointMS {T : Sylow 2 G}
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Earlier14710At T := by
  intro L V F _ h _
  exact OriginalSourceAt.chief_bound_or_baumann_normalizer_of_naturalPointMS h structural F

end OriginalSource
end ResidualNormalizer.LocalControl
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
