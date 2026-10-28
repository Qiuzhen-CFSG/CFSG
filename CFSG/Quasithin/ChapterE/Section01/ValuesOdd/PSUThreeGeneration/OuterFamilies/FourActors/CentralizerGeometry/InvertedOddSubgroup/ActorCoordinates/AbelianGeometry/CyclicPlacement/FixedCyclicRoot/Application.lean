module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.FixedCyclicRoot

/-!
# Application of the fixed torus calculation to cyclic actor placement

The root coordinate premise of `cyclicInnerPlacement_of_fixed_geometry`
is discharged by the proved fixed cyclic torus placement and root action
when p is 1 modulo four. Only the independent fixed-involution extension
remains explicit in that application, for the order-two inner preimage.
The more general conditional torus-to-root application is retained.
Source: Aschbacher--Smith E.1.14(7), printed p.214; Aschbacher (1982),
Lemma 4.11.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
variable {F : Type} [Field F] [Finite F]

/-- Feed the fixed torus calculation into the literal cyclic-placement consumer. -/
theorem cyclicInnerPlacement_of_fixed_torusPlacement
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hext : FixedInvolutionExtension J) (hplace : FixedCyclicTorusPlacement J hJ) :
    CyclicInnerPlacement J := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  have h2 : (2 : F) ≠ 0 :=
    HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.two_ne_zero_of_prime_square
      hp hp3 hcard
  exact cyclicInnerPlacement_of_fixed_geometry J hp ho hcard hc hJ hext
    (fixedCyclicRootCoordinates_of_torusPlacement J hJ h2 hplace)

/-- Discharge the larger cyclic branch, retaining only the independent
fixed-involution extension for the order-two branch. -/
theorem cyclicInnerPlacement_of_fixed_involution_extension
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hext : FixedInvolutionExtension J) :
    CyclicInnerPlacement J := by
  exact cyclicInnerPlacement_of_fixed_geometry J hp ho hcard hc hJ hext
    (fixedCyclicRootCoordinates J hp ho hmod hcard hc hJ)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
