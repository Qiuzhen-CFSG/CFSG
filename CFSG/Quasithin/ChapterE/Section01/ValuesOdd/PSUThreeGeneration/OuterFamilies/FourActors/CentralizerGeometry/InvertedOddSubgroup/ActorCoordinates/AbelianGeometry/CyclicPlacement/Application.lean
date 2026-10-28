module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement

/-!
# Application of the cyclic reduction to abelian outer coordinates

The fixed-involution extension and fixed cyclic root inputs supply the exact
`CyclicInnerPlacement` premise of the existing abelian-coordinate consumer.
The original conditional application is retained. For p one modulo four,
the final application discharges both matrix existence inputs with the proved
cyclic placement theorem. Only the independent standard-four fixer premise
remains explicit.

Source: Aschbacher--Smith E.1.14(7), printed p.214; Aschbacher (1982),
Lemma 4.11. This is conditional assembly, not completion of the source result.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
open AbelianGeometry AbelianGeometry.CyclicPlacement
open InnerGeometry.SemidihedralTorus
variable {F : Type} [Field F] [Finite F]

/-- Apply the fixed-field cyclic reduction while retaining the independent
standard-four fixer input. -/
theorem abelianOuterCoordinateGeometry_of_fixed_cyclic_geometry
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hfix : StandardFixerCoordinates (HermitianForm.IdentityGram.identityGram J))
    (hext : FixedInvolutionExtension J) (hroot : FixedCyclicRootCoordinates J) :
    AbelianOuterCoordinateGeometry J := by
  exact abelianOuterCoordinateGeometry_of_cyclicInnerPlacement J hp ho hcard hc hJ hfix
    (cyclicInnerPlacement_of_fixed_geometry J hp ho hcard hc hJ hext hroot)

/-- Discharge cyclic inner placement in the abelian-coordinate consumer.
Only the independent standard-four fixer premise remains. -/
theorem abelianOuterCoordinateGeometry_of_standardFixerCoordinates
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hfix : StandardFixerCoordinates (HermitianForm.IdentityGram.identityGram J)) :
    AbelianOuterCoordinateGeometry J := by
  exact abelianOuterCoordinateGeometry_of_cyclicInnerPlacement J hp ho hcard hc hJ hfix
    (cyclicInnerPlacement J hp ho hmod hcard hc hJ)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
