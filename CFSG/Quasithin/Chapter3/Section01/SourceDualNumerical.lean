module
public import CFSG.Quasithin.Chapter3.Section01.SourceDualOffenderInput
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.Complete

/-!
# The original qrc dual-FF numerical branch

The dual FF witness makes its normal offender subgroup nontrivial. The
original qrc action supplies every B.5 source hypothesis there, including
an actual SQTK cover. The complete B.5.13 bound transfers back along the
literal inclusion and bounds the original cubic ratio by two.

Source: Aschbacher--Smith B.5.13 and 3.1.6--8, printed pp.110--112,573--576.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- B.5.13 bounds the literal original qrc action whenever its dual is FF. -/
theorem QrcHypotheses.quadraticRatio_le_two_of_dualFF
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hdual : letI := h.module_elementary
      IsFFModule (imageRepresentation M₀ V h.module_normalized).dual) :
    letI := h.module_elementary
    quadraticRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  let := h.module_elementary
  let ρ := imageRepresentation M₀ V h.module_normalized
  let N := offenderSubgroup ρ.dual
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr
    (offenderSubgroup_ne_bot_of_ff ρ.dual hdual)
  exact h.quadraticRatio_le_dual_offender_restriction.trans
    (ChapterB.SourceB513.quadraticRatio_le_two_of_source (ρ.comp N.subtype)
      (h.dual_offender_source hG hM))

/-- The dual-FF branch supplies the original cubic numerical bound. -/
theorem QrcHypotheses.cubicRatio_le_two_of_dualFF
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hdual : letI := h.module_elementary
      IsFFModule (imageRepresentation M₀ V h.module_normalized).dual) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  let := h.module_elementary
  exact (cubicRatio_le_quadraticRatio _).trans
    (h.quadraticRatio_le_two_of_dualFF hG hM hdual)

/-- The literal `DualFF` alternative of the original qrc configuration is discharged. -/
theorem QrcHypotheses.cubicRatio_le_two_of_literal_dualFF
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hdual : DualFF (h.toQRCConfiguration (h.no_common_normal hu))) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 :=
  h.cubicRatio_le_two_of_dualFF hG hM hdual
end CFSG.Quasithin.Chapter3
