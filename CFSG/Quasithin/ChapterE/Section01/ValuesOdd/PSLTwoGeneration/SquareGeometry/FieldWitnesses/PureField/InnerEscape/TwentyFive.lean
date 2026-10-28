module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.FixedCentralizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry

/-!
# Characteristic-five inner-model escape

The five-element projective quotient is identified with the actual symmetric
group on five letters. Its PSL₂ layer is marked as A₅, and generation for
positioned actors is lifted through the normal two-kernel and E.1.8.
The proved actor fusion and centralizer/normalizer joins position an original
family actor in a centralizer outside each proposed proper overgroup. This
discharges the geometric premise and gives escape at every Sylow subgroup,
retaining both ranks of actors and every invariant family.

The only remaining premise is the positioned outer-four S₅ input. Its producer
is `ValuesOdd/PSUThreeGeneration/OuterFamilies/EightActors/CentralizerContainment/
FiveGeneration.lean`; the full canonical-model assembly must discharge it.

Source: Aschbacher--Smith E.1.2, E.1.5, E.1.8 and E.1.14(6), printed
pp.210--214; Aschbacher (1982), Lemma 4.10.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive
open Subgroup GorensteinWalter Matrix
variable {F : Type*} [Field F] [Finite F]

/-- The five-point model premise is discharged; only the independent finite
actor/fusion geometry and the task's permitted S5 input remain. -/
theorem escape_of_geometry (hF : Nat.card F = 5 ^ 2)
    (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) [Finite (innerModel F σ)]
    (hgeometry : HasPositionedCentralizerGeometry hF σ
      ((orderOf_eq_prime_iff (x := σ)).mpr ⟨hsq, hne⟩))
    (hfive : FiveGeneration) :
    ∀ T : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt T := by
  obtain ⟨e⟩ := Theory.PSL2.exists_pgl2_five_equiv (FixedPoints.subfield (zpowers σ) F)
    (fixedSubfield_card hF σ hsq hne)
  exact escape_of_marked_projective_and_geometry hF σ hsq hne e hgeometry hfive

/-- Characteristic-five escape for every Sylow subgroup in the actual inner
model. The actor positioning, fusion and weak-closure normalizer geometry are
discharged. Only the specified smaller-group S₅ generation input remains;
the intrinsic quotient ranks, literal Sylow intersections and E1/E2 clauses
are those of `LargeFamilyEscapeAt`. -/
theorem escape (hF : Nat.card F = 5 ^ 2)
    (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) [Finite (innerModel F σ)]
    (hfive : FiveGeneration) :
    ∀ T : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt T := by
  exact escape_of_geometry hF σ hsq hne
    (Geometry.hasPositionedCentralizerGeometry hF σ
      ((orderOf_eq_prime_iff (x := σ)).mpr ⟨hsq, hne⟩)) hfive

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive
