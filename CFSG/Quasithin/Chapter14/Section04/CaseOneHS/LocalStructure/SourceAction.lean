module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.CoreMovement
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.SolvableExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.SmallCenter
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.DottedNatural
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure

/-!
# Assembling the natural HS action branch

Natural coordinates suffice for ActionStructure: source geometry constructs
the cyclic-four center, and the original embedded solvable residual supplies
all component clauses. Applying the published local assembly then constructs
the embedded quaternion factors and the exact action kernel.

This is checked partial assembly of 14.3.32. SmallCenter excludes the literal
S₃ × S₃ alternative, deriving the needed order and relative-normality premises
from its actual dotted quotient. The separately imported EarlierGeometry extension supplies the genuine
marked classification inputs and
14.3.23 geometric clauses without centerlessness. DottedNatural derives the
two-core kernel from the actual faithful natural row. Construction of that
row, the source action alternatives, and their remaining exclusions remain
with qt-d-hs-action-source. The preceding centerlessness premise is discharged by
qt-d-hs-local-structure. The older conditional component interfaces are preserved.

Source: Aschbacher--Smith, 14.3.32, printed pp.1003--1004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Discharge the two center fields of the published action contract. The
remaining natural-action and component conclusions are explicit premises. -/
theorem actionStructure_of_natural_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F)
    (component : ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      F.H = K ⊔ (T : Subgroup G) ∧ F.U = ⁅K.pCoreIn 2, K⁆ ∧
      TildeIndecomposable F K) : ActionStructure F := by
  obtain ⟨hcyclic, hcard⟩ := source_center_of_natural d earlier hq chosen structural
    alternatives F hne hI hc
  exact ⟨hc, hcyclic, hcard, component⟩

/-- Literal local-structure consumer of the constructed action contract. -/
theorem localStructure_of_natural_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F)
    (component : ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      F.H = K ⊔ (T : Subgroup G) ∧ F.U = ⁅K.pCoreIn 2, K⁆ ∧
      TildeIndecomposable F K) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne hI
    (actionStructure_of_natural_component d earlier hq chosen structural alternatives
      F hne hI hc component)


/-- Construct every action-structure field from the actual natural coordinates.
The source alternative exclusions, hence those coordinates, remain to be proved. -/
theorem actionStructure_of_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F) :
    ActionStructure F :=
  actionStructure_of_natural_component d earlier hq chosen structural alternatives F hne hI hc
    (source_component_of_natural d earlier hq chosen structural alternatives F hne hZ hI hc)

/-- Apply the constructed action to the literal local-structure consumer. -/
theorem localStructure_of_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F) :
    LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne hI
    (actionStructure_of_natural d earlier hq chosen structural alternatives F hne hZ hI hc)

/-- Apply the proved natural-row kernel bridge to the published action contract. -/
theorem actionStructure_of_dotted_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : DottedNaturalCoordinates F) : ActionStructure F :=
  actionStructure_of_natural d earlier hq chosen structural alternatives F hne hZ hI
    (source_naturalCoordinates_of_dotted d earlier hq chosen structural alternatives F hne hZ hI hc)

/-- Literal local-structure application of the faithful natural row. -/
theorem localStructure_of_dotted_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : DottedNaturalCoordinates F) : LocalStructure L F :=
  localStructure_of_natural d earlier hq chosen structural alternatives F hne hZ hI
    (source_naturalCoordinates_of_dotted d earlier hq chosen structural alternatives F hne hZ hI hc)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
