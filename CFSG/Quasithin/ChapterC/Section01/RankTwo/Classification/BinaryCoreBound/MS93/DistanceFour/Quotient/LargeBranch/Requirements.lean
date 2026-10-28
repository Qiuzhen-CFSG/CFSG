module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.FirstFactor

/-!
# The two remaining source constructions in MS93 (4.6.12)

`FirstStep` asks for the first actual marked factor and the literal order
|V_alpha^*/Z_alpha| = 2^6 from (1)--(5), pp.910--912. `SecondStep` asks for
the reapplication to a selected noncommuting Z_rho and the printed identity
V_alpha^* = V_0 <Z_rho^{G_alpha}> on p.912. It takes the uniform first-stage
construction explicitly, so the two proofs can be developed independently.

These propositions have no constructors here. In particular neither is an
additional source hypothesis or a proof of the original theorem. The final
assembly must construct both from LocalSource, Geometry, CommonFacts,
RadiusFacts and b = 4, then discharge them.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- The rank-one construction (1)--(5), including the actual first factor
inside the core and the source's starred quotient order. -/
def FirstStep : Prop :=
  ∀ s : CriticalSegment geometry, ¬ s.SmallIntersection →
    Nonempty (FirstFactor source common s.middle) ∧
      (Z R (alpha R)).relIndex (VStar R geometry (alpha R) (beta R)) = 64

/-- Reapply the first construction at the selected noncommuting vertex and
prove the actual two-span generation identity. No core-center premise occurs. -/
def SecondStep : Prop :=
  FirstStep source common →
    ∀ (s : CriticalSegment geometry), ¬ s.SmallIntersection →
      ∀ (_f : FirstFactor source common s.middle) (rho : Vertex R),
        nu R geometry (alpha R) rho → Adjacent R (beta R) rho →
        ⁅Z R rho, orbitSpan s.middle⁆ ≠ ⊥ →
        Nonempty (FirstFactor source common rho) ∧
          VStar R geometry (alpha R) (beta R) = orbitSpan s.middle ⊔ orbitSpan rho

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
