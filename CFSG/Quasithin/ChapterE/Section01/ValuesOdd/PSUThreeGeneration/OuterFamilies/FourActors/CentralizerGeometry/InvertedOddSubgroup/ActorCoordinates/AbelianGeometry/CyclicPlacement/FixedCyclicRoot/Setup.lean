module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.Setup

/-!
# The remaining fixed cyclic torus placement problem

The torus uses units of the stored Hermitian involution's literal fixed
subfield. The geometric input asks only to conjugate a fixed cyclic
two-group generator into that torus by a fixed projective element. It does
not assume an action on a root line or a marking of its involution.

The consumer in `FixedCyclicRoot` derives both conclusions. This is an
explicit intermediate contract; existence of the conjugator remains a
separate proof obligation.
Source: Aschbacher--Smith E.1.14(7), printed p.214, and A.3.21(a)--(b),
printed p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
variable {F : Type} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

namespace FixedCyclicRoot
/-- The Hermitian diagonal torus restricted to the original fixed field. -/
@[expose] def fixedTorus : (FixedBy.subfield F J.conj)ˣ →*
    ProjectiveSpecialUnitaryMatrixGroup J :=
  (hermitianTorusPSU J hJ).comp
    (Units.map (FixedBy.subfield F J.conj).subtype.toMonoidHom)


end FixedCyclicRoot

/-- Fixed conjugacy of a larger cyclic two-group into the literal split torus.
The involution marking and all actor formulas are proved by its consumer. -/
@[expose] def FixedCyclicTorusPlacement : Prop :=
  ∀ γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
    J.IsEntrywiseConjugation γ →
    ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      γ x = x → IsPGroup 2 (zpowers x) → 2 < orderOf x →
    ∃ y : ProjectiveSpecialUnitaryMatrixGroup J, γ y = y ∧
      ∃ c : (FixedBy.subfield F J.conj)ˣ,
        MulAut.conj y x = FixedCyclicRoot.fixedTorus J hJ c

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
