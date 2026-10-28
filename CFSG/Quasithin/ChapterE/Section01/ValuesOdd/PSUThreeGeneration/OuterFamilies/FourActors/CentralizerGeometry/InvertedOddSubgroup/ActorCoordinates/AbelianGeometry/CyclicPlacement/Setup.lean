module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicSetup

/-!
# Fixed-field matrix inputs for cyclic inner placement

The actor decomposition separates two matrix problems. A fixed involution
must extend to a pair of distinct commuting fixed involutions. A larger
fixed cyclic two-group must admit root coordinates for its inner image
and entrywise conjugation. The latter coordinates retain the original
field and involution and control the literal generated actor subgroup.

These are explicit unproved intermediate contracts, not source theorems.
Their conditional consumer is `cyclicInnerPlacement_of_fixed_geometry`.
Source: Aschbacher--Smith E.1.14(7), printed p.214, and A.3.21(a)--(b),
printed p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
variable {F : Type} [Field F]

/-- A fixed involution extends to two distinct commuting fixed involutions. -/
@[expose] def FixedInvolutionExtension (J : HermitianForm 3 F) : Prop :=
  ∀ γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
    J.IsEntrywiseConjugation γ →
    ∀ w : ProjectiveSpecialUnitaryMatrixGroup J, orderOf w = 2 → γ w = w →
    ∃ v : ProjectiveSpecialUnitaryMatrixGroup J,
      orderOf v = 2 ∧ v ≠ w ∧ γ v = v ∧ Commute w v

/-- A fixed cyclic two-group of order greater than two admits literal root
coordinates for its inner image together with entrywise conjugation. -/
@[expose] def FixedCyclicRootCoordinates (J : HermitianForm 3 F) : Prop :=
  ∀ γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
    J.IsEntrywiseConjugation γ →
    ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      γ x = x → IsPGroup 2 (zpowers x) → 2 < orderOf x →
    ∀ w : ProjectiveSpecialUnitaryMatrixGroup J, orderOf w = 2 → w ∈ zpowers x →
      RootActionCoordinates J ((zpowers x).map MulAut.conj ⊔ zpowers γ) w

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
