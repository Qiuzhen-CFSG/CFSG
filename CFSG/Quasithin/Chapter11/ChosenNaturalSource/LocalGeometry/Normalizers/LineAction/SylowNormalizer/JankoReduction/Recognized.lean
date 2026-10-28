module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.FieldFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.InnerAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Fixer

/-!
# Applying a recognized component to the literal J₁ terminal configuration

The moved normal component retains the actual flag residual, odd supplement,
and enlarged parabolic. Its J₁ quotient forces field degree two and the inner
T-action, by the preceding cardinality and Sylow-action arguments. Thus the
terminal configuration needs only recognition of that quotient and escape of
K intersect A. The two terminal consumers use the literal section centralizer
and displacement, with their component normalization already proved.

The quotient recognition, intersection escape, and remaining SL₃/Sp₄/G₂
terminal geometry are obligations of qt-d-1222-natural-line-action. These
conditional consumers do not assert Sylow-normalizer containment or 11.2.3.
Source: Aschbacher--Smith, 3.3.15--16, printed pp.590--591.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)
    (e : E.component ⧸ pCore 2 E.component ≃* Janko1.Model)
    (hout : ¬ E.component ⊓ A.subgroup ≤ normalizer (L : Set G))

/-- The field and inner-action clauses are proved from the actual J₁ quotient. -/
def jankoConfiguration : JankoConfiguration S f A where
  index := E.index
  degree_eq_two := degree_eq_two_of_janko_containing E.index E.contains.le e
  component := E.component
  parabolic := (invariantFlag_geometry D S f).2.2.parabolic E.index
  moves := E.moves
  contains := E.contains
  normal_component := E.normal_component
  model := ⟨e⟩
  outside := hout
  inner := residual_action_inner_of_janko_containing E.index E.contains.le
    (le_sup_right.trans le_sup_left |>.trans E.local_normalizes) e

/-- The constructed configuration feeds the SL₃ common-normal contradiction. -/
theorem false_of_recognized_common_normal
    (hne : (E.jankoConfiguration e hout).oddSectionCentralizer ≠ ⊥)
    (hLQ : L ≤ normalizer ((E.jankoConfiguration e hout).displacement : Set G)) : False :=
  (E.jankoConfiguration e hout).false_of_displacement_normalized_by_L hne hLQ

/-- The same constructed configuration feeds the Sp₄ small-action contradiction. -/
theorem false_of_recognized_small_displacement
    (hsmall : Nat.card (E.jankoConfiguration e hout).displacement ≤ 2 ^ 16)
    (hmoves : ¬ f.Li E.index ≤ centralizer ((E.jankoConfiguration e hout).displacement : Set G)) :
    False :=
  (E.jankoConfiguration e hout).false_of_small_moved_displacement hsmall hmoves

end MovedComponent
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
