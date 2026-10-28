module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.CenterAssembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Second
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Kernel.Source

/-!
# The exact source distance-four quotient and center

The source common facts and distance four supply the early and radius facts.
The proved small-intersection argument excludes that branch. In the large
branch, full-span recognition supplies both marked quotients by Z_alpha and
the starred index. The second-stage construction reapplies the first stage
and supplies generation, so the two factors yield the actual whole-core map.

The source moving-kernel theorem uses the opposite midpoint core to exclude
a fixed central attachment, proving that the moving span meets Z_alpha in
U_alpha. The resulting whole-core map has exactly U_alpha as kernel. The
commutator-pairing argument then identifies the full core center with U_alpha.
The final source theorems require only LocalSource, Geometry, CommonFacts and
b = 4; the earlier conditional interfaces are retained.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.11)--(4.6.12), printed pp.909--912.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- All source branch inputs except the exact moving-span kernel are discharged. -/
theorem doubleDualQuotient_of_movingKernel (hb : geometry.b R = 4)
    (hker : LargeBranch.RankOne.MovingKernelControl source common) :
    Nonempty (DoubleDualQuotient source common) := by
  let early := earlyFacts source geometry common hb
  let radius := Flags.radiusFacts source geometry common hb early
  apply doubleDualQuotient_of_local_branches source common radius hb
    (singleQuotient_of_smallIntersection source geometry common radius hb)
  exact LargeBranch.orbitFactors_of_steps radius
    (LargeBranch.firstStep_of_source_recognition_and_movingKernel common radius hb hker)
    (LargeBranch.secondStep source common radius hb)

/-- The same single remaining geometric input gives the source's exact center. -/
theorem center_core_of_movingKernel (hb : geometry.b R = 4)
    (hker : LargeBranch.RankOne.MovingKernelControl source common) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype = U R (alpha R) := by
  obtain ⟨d⟩ := doubleDualQuotient_of_movingKernel source common hb hker
  exact d.center_core

/-- The original binary distance-four source yields the whole-core quotient
by literal U_alpha, with both dual factors under the supplied natural marking. -/
theorem source_doubleDualQuotient (hb : geometry.b R = 4) :
    Nonempty (DoubleDualQuotient source common) := by
  let early := earlyFacts source geometry common hb
  let radius := Flags.radiusFacts source geometry common hb early
  exact doubleDualQuotient_of_movingKernel source common hb
    (LargeBranch.RankOne.source_movingKernelControl common radius hb)

include source common in
/-- The center conclusion of original MS93 (4.6) in the binary case. -/
theorem source_center_core (hb : geometry.b R = 4) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype = U R (alpha R) := by
  obtain ⟨d⟩ := source_doubleDualQuotient source common hb
  exact d.center_core

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
