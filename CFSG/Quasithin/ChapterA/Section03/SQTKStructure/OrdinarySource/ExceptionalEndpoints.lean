module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Alternating
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
/-!
# ExceptionalEndpoints ordinary components in A.3.6

The genuine exceptional isomorphisms recover the A₆ quotient in PSL₂(9)
and in the literal PSp₄(2) commutator subgroup. The alternating covering
theorem retains the possible central triple covers.
Every branch supplies the full common Fitting and radical conclusion.

Source: Aschbacher–Smith A.3.6 and I.1.3, printed pp.43–45, 407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02

/-- The exceptional odd PSL₂ parameter is A₆; its possible triple cover
is retained exactly as in the alternating source branch. -/
theorem a36_psl2_nine {X : Type*} [Group X] [Finite X]
    (hcore : pCore 2 X = ⊥) (L : Subgroup X) (hL : IsComponent X L)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 9)
    (e : L ⧸ center L ≃* PSL(2,F)) : A36Conclusion L :=
  a36_alternating hcore L hL 6 (by decide)
    (e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF))

/-- The literal commutator carrier PSp₄(2)′ has the actual A₆ quotient
model, including its allowed central triple cover upstairs. -/
theorem a36_symplectic_derived {X : Type*} [Group X] [Finite X]
    (hcore : pCore 2 X = ⊥) (L : Subgroup X) (hL : IsComponent X L)
    (e : L ⧸ center L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    A36Conclusion L :=
  a36_alternating hcore L hL 6 (by decide)
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
