module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.FixedInvolution

/-!
# Cyclic inner placement with the fixed-involution premise discharged

The proved fixed-involution extension supplies the small-inner-preimage
branch of `cyclicInnerPlacement_of_fixed_geometry`. The independent
`FixedCyclicRootCoordinates` premise remains explicit; its discharge and
final source assembly belong to the parent cyclic-placement task.

Source: Aschbacher--Smith E.1.14(7), printed p.214; A.3.21(a)--(b), printed
p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
variable {F : Type} [Field F] [Finite F]

/-- The cyclic actor reduction with the fixed-involution geometry proved.
Only the independent fixed cyclic root coordinates remain as geometric input. -/
theorem cyclicInnerPlacement_of_fixedCyclicRootCoordinates
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hroot : FixedCyclicRootCoordinates J) : CyclicInnerPlacement J :=
  cyclicInnerPlacement_of_fixed_geometry J hp ho hcard hc hJ
    (fixedInvolutionExtension J hp ho hcard hJ) hroot

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
