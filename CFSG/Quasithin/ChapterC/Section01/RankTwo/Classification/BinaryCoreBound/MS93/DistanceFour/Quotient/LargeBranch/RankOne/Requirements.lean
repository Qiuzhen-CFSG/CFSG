module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Moving

/-!
# Remaining recognition and moving-kernel obligations

`SpanRecognition` is the literal full-span output of MS93 (1993),
(4.6.12)(1)--(5), printed pp.910--912: containment in the midpoint kernel,
the marked dual quotient by Z_alpha, and the starred index 64.

`MovingKernelControl` is the separate conversion needed for the core factor:
the moving span meets Z_alpha in exactly U_alpha. It takes the recognized
span and starred index as explicit inputs so the two arguments can be
developed independently. Neither proposition has a source constructor here.
Final assembly must prove both from LocalSource, CommonFacts, RadiusFacts,
the critical segment, and b = 4.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- The original full-span recognition and the literal starred index in (5). -/
def SpanRecognition : Prop :=
  ∀ s : CriticalSegment geometry, ¬ s.SmallIntersection →
    orbitSpan s.middle ≤ Q R s.middle ∧
      Nonempty (SpanQuotient source common s.middle) ∧
        (Z R (alpha R)).relIndex (VStar R geometry (alpha R) (beta R)) = 64

/-- The remaining exact-kernel assertion for the canonical moving subgroup. -/
def MovingKernelControl : Prop :=
  ∀ s : CriticalSegment geometry, ¬ s.SmallIntersection →
    orbitSpan s.middle ≤ Q R s.middle →
    SpanQuotient source common s.middle →
    (Z R (alpha R)).relIndex (VStar R geometry (alpha R) (beta R)) = 64 →
    movingSpan s.middle ⊓ Z R (alpha R) = U R (alpha R)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
