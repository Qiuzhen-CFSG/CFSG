module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction

/-!
# The precise C.2.7 alternative still used by Rudvalis recognition

For each actual fixed-element centralizer, the original source construction
supplies the C.2.3 input on its relatively normal component. The proved
C.2.7(1)--(2) theorem then supplies the kernel and offender conclusions on
the same star quotient. Only the geometric alternatives of C.2.7(3) remain
explicit, and the original 14.7.75 application consumes them immediately.

Source: Aschbacher--Smith C.2.7, printed pp.145--147, and the nonquasisimple
component paragraph of 14.7.68(2), printed pp.1071--1072.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- C.2.7(3) only, on the actual relatively normal fixed components. -/
@[expose] def FixedComponentAlternatives (d : Data T L V F W) : Prop :=
  ∀ (u : F.U) (Lu : Subgroup G), Nonquasisimple.Case d u Lu →
    FullSieve.SourceInterface.Alternatives KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)

/-- The literal source input discharges both other clauses of C.2.7. -/
theorem fixedComponentClassification_of_alternatives (d : Data T L V F W)
    (alternatives : FixedComponentAlternatives d) : FixedComponentClassification d := by
  intro u Lu h
  have input := d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
    d.point_mem_U_commutator_K
  obtain ⟨kernel, offenders⟩ := ChapterC.C27Source.kernel_offender_from_source input
  exact ⟨kernel, offenders, alternatives u Lu h⟩

variable (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
  (baumann : ResidualNormalizer.LocalControl.Earlier14710.{u})
  (weakClosure : Theorem14731.{u})
  (alternatives : FixedComponentAlternatives d)
include d structural faithful modules baumann weakClosure alternatives

/-- Rudvalis recognition with only the local geometric C.2.7 alternatives. -/
theorem source_rudvalis_of_local_alternatives : Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_earlier_inputs d structural faithful modules baumann weakClosure
    (fixedComponentClassification_of_alternatives d alternatives)

/-- The same actual isomorphism supplies the full D-model conclusion. -/
theorem source_theoremDModel_of_local_alternatives : ClassificationModels.IsTheoremDModel G :=
  source_theoremDModel_of_earlier_inputs d structural faithful modules baumann weakClosure
    (fixedComponentClassification_of_alternatives d alternatives)

omit weakClosure in
/-- The original Rudvalis application with both clauses of 14.7.31 proved.
The earlier structural, classification and Baumann producers remain explicit. -/
theorem source_rudvalis_of_local_alternatives_source14731 : Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_local_alternatives d structural faithful modules baumann
    (source_theorem14731 structural) alternatives

omit weakClosure in
/-- The same source isomorphism discharges the D-model consumer's weak-closure input. -/
theorem source_theoremDModel_of_local_alternatives_source14731 :
    ClassificationModels.IsTheoremDModel G :=
  source_theoremDModel_of_local_alternatives d structural faithful modules baumann
    (source_theorem14731 structural) alternatives

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
