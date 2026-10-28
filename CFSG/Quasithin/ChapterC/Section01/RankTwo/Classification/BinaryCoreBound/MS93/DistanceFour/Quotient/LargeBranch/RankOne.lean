module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Requirements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Requirements

/-!
# Conditional first-stage assembly for MS93 (4.6.12)

The midpoint geometry supplies the noncentral vertex and span. Once the
full-span quotient is recognized and the moving subgroup's intersection
with Z_alpha is proved to be U_alpha, restrict the quotient to that actual
core subgroup. This constructs its onto map, exact relative kernel and
contragredient action, and all remaining FirstFactor fields.

The source recognition and moving-kernel constructors are still separate
proof obligations. The theorem below does not discharge either or claim
the unconditional FirstStep. Source: original MS93 (1993), (4.6.12)(1)--(5),
printed pp.910--912.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- The canonical moving subgroup gives the required first factor once its
intersection with Z_alpha has been computed. -/
noncomputable def firstFactor_of_moving_kernel (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (q : RankOne.SpanQuotient source common s.middle)
    (hspan : orbitSpan s.middle ≤ Q R s.middle)
    (hker : RankOne.movingSpan s.middle ⊓ Z R (alpha R) = U R (alpha R)) :
    FirstFactor source common s.middle :=
  let d := RankOne.movingCoreLift common s.middle s.first_distance q hker
  { factor := d.factor
    factor_le := d.factor_le
    data := d.dualFactor q
    vertex_nu := RankOne.midpoint_nu common radius hb s
    span_le_kernel := hspan
    span_not_le_Z := RankOne.midpoint_span_not_le_Z common radius hb s
    span_decomposition := d.decomposition }

/-- Assemble the first stage after both independent source obligations have
been proved. Neither input is constructed by this conditional theorem. -/
theorem firstStep_of_recognition_and_movingKernel (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (hrec : RankOne.SpanRecognition source common)
    (hker : RankOne.MovingKernelControl source common) : FirstStep source common := by
  intro s hs
  obtain ⟨hspan, ⟨q⟩, hindex⟩ := hrec s hs
  exact ⟨⟨firstFactor_of_moving_kernel source common radius hb s q hspan
    (hker s hs hspan q hindex)⟩, hindex⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
