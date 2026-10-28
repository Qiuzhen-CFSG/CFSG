module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.Setup
public import Theory.SpecificGroups.SU3.OrthogonalFixed.CommutingInvolutions
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.FirstField

/-!
# Fixed-involution extension for cyclic inner placement

A reflection of the negative eigenspace in the actual fixed orthogonal group
supplies a commuting partner for every entrywise fixed projective involution.
This discharges `FixedInvolutionExtension`, including the order-two inner
preimage case of the parent cyclic reduction. The separate cyclic root
coordinates are retained by the consumer in `FixedInvolution.Application`.

Source: Aschbacher--Smith E.1.14(7), printed p.214, A.3.21(a)--(b), printed
p.55; Aschbacher (1982), Lemma 4.11. This proves the fixed-involution input,
not the whole source theorem.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
variable {F : Type} [Field F]

/-- Every entrywise fixed projective involution has a distinct commuting
entrywise fixed involution, over any field of characteristic different from two. -/
theorem fixedInvolutionExtension_of_two_ne_zero
    (J : HermitianForm 3 F) (h2 : (2 : F) ≠ 0)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) : FixedInvolutionExtension J := by
  intro γ hγ w hw hfix
  exact HermitianForm.OddPrimeSylow.projective_fixed_involution_extension
    J h2 hJ γ hγ w hw hfix

/-- The fixed-involution input in the odd-prime unitary branch. Simplicity,
the Frobenius formula and the congruence modulo four are not needed here. -/
theorem fixedInvolutionExtension [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) : FixedInvolutionExtension J := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  exact fixedInvolutionExtension_of_two_ne_zero J
    (HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.two_ne_zero_of_prime_square
      hp hp3 hcard) hJ

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
