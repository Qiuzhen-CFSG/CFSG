module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupTheory.MaximalTwoLocalOvergroups

/-!
# The seven module alternatives in original Theorem 12.2.2

These are assertions about the literal chosen Irr⁺ subspace, its conjugation
action, and its quotient by the L-fixed space. The two acting quotients
L/O₂(L) and L/C_L(V) are kept distinct. The last row uses the concrete even
hexacode automorphism group, the triple cover of A₆. Structural1222 remains
the separate structural prefix and does not assert these alternatives.

Source: Aschbacher--Smith, Theorem 12.2.2(3a--g), printed p.795.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The seven original alternatives, including actual module identifications
where the source specifies a natural module, and literal actions everywhere. -/
inductive ModuleAlternatives1222 (D : ChosenModule T L V) : Prop
  | linear (n : ℕ) (degree : n = 3 ∨ n = 4 ∨ n = 5)
      (action : ActionEquiv D.quotientAction (specialLinearNatural (k := ZMod 2) n))
  | linearThreeExtension
      (groupEquiv : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (dimension : Module.finrank (ZMod 2) D.space = 4)
      (indecomposable : IsIndecomposable D.quotientAction)
  | linearFiveExterior
      (groupEquiv : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
      (dimension : Module.finrank (ZMod 2) D.space = 10)
      (irreducible : IsIrreducible D.quotientAction)
  | alternating (n : ℕ) (lower : 5 ≤ n) (upper : n ≤ 8)
      (action : letI := D.actionCentralizer_normal
        ActionEquiv D.faithfulCentralAction (alternatingNatural n))
  | alternatingSevenFour
      (groupEquiv : letI := D.actionCentralizer_normal
        (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2) D.space = 4)
  | g2
      (action : ActionEquiv D.centralQuotientAction
        ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype))
  | tripleSix
      (groupEquiv : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
      (dimension : Module.finrank (ZMod 2) D.space = 6)
      (faithful : Function.Injective D.quotientAction)
      (irreducible : IsIrreducible D.quotientAction)

/-- The module-classification implication, separate from Structural1222.
It is an outstanding source target, not an assumed classification field in
Hypothesis1223 or ChosenModule. -/
def Theorem1222Modules (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    Hypothesis1223 K T L → (D : ChosenModule T L V) → ModuleAlternatives1222 D

/-- The source classification specialized to the multiple-overgroup branch
actually used in Theorem D. This does not assert the universal implication. -/
def Theorem1222ModulesOfMany (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    1 < (maximalTwoLocalOvergroups (T : Subgroup X)).ncard →
    Hypothesis1223 K T L → (D : ChosenModule T L V) → ModuleAlternatives1222 D

end CFSG.Quasithin.Chapter12.Section02
