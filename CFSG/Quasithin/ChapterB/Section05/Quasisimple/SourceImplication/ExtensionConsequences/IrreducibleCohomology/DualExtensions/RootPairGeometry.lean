module
public import Theory.Representation.G2NaturalOffenders
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.NonbinaryTrace

/-!
# The genuine G₂ root-pair producer for B.5.1

The classification of offenders on the actual natural octonion quotient
identifies every offender with one conjugate of the concrete A–B–C group.
Both prescribed roots therefore occur with the same conjugator. This
removes the placement premise of `NonbinaryTrace` and supplies its trace
detection theorem on the literal `binaryG2` action. Rank, fixed codimension
and quadratic ratio are recorded for the same action.

Source: Aschbacher–Smith B.4.6(13), printed pp.88–90, and B.5.1(5),
printed pp.102–103. The argument includes the binary field.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions

/-- The common root-pair placement in B.4.6(13), on the literal B.5.1 action. -/
theorem g2_bestOffender_rootPair (F : BinaryField) : G2BestOffenderRootPair F := by
  intro A hA
  exact Atlas.G2.NaturalOffenders.natural_offender_rootPair F.card_eq F.degree_pos A
    (hA.isOffender (binaryG2 F))

/-- Every binary natural G₂ offender is a conjugate of the concrete A–B–C subgroup. -/
theorem g2_bestOffender_classification (F : BinaryField) (A : Subgroup (Atlas.G2.Model F.Carrier)) :
    IsBestOffender (binaryG2 F) A ↔ ∃ g : Atlas.G2.Model F.Carrier,
      A = (Atlas.G2.EvenTwoRank.elementary F.Carrier).map (MulAut.conj g).toMonoidHom :=
  Atlas.G2.NaturalOffenders.natural_bestOffender_iff_conjugate F.card_eq F.degree_pos A

/-- The exact rank and fixed codimension required by the G₂ row of B.5.1. -/
theorem g2_offender_rank_and_fixedCodim (F : BinaryField)
    (A : Subgroup (Atlas.G2.Model F.Carrier)) (hA : IsOffender (binaryG2 F) A) :
    rank A = 3*F.degree ∧ fixedCodim (binaryG2 F) A = 3*F.degree :=
  ⟨Atlas.G2.NaturalOffenders.natural_offender_rank F.card_eq F.degree_pos A hA,
   Atlas.G2.NaturalOffenders.natural_offender_fixedCodim F.card_eq F.degree_pos A hA⟩

/-- The ratio assertion for the actual inner G₂ natural action. -/
theorem g2_quadraticRatio (F : BinaryField) : quadraticRatio (binaryG2 F) = 1 :=
  Atlas.G2.NaturalOffenders.natural_quadraticRatio F.card_eq F.degree_pos

/-- The previously explicit placement premise in `NonbinaryTrace` is now discharged. -/
theorem g2_traceDetection (F : BinaryField) : G2TraceDetection F :=
  g2_traceDetection_of_bestOffender_rootPair F (g2_bestOffender_rootPair F)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions
