module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry
/-!
# Application to the original faithful normal subgroup and whole actor

This leaf supplies hgeometry in hasInvertedCoordinates_of_abelian_action
from the two independent model inputs. It retains the original faithful
normal subgroup, abelian two-group, outer involution and marked inner
involution. The identity Gram model inherits simplicity through the actual
projective equivalence.

Final discharge remains with the owning task: the standard-fixer producer
is qt-e01-odd-psu3-standard-fixer-coordinates, and the cyclic branch producer
is qt-e01-odd-psu3-cyclic-inner-outer-placement. Their intended source domain
is p congruent to one modulo four. This conditional application does not
assert that either missing geometric input has been proved.
Source: Aschbacher--Smith E.1.14(7), printed p.214; Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
open InnerGeometry.SemidihedralTorus
open AbelianGeometry
variable {G : Type*} [Group G]
/-- Discharge the exact ambient coordinate premise using both model inputs. -/
theorem hasInvertedCoordinates_of_cyclicInnerPlacement
    (L R : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (hfaithful : centralizer (L : Set G) = ⊥)
    (hR : IsPGroup 2 R) [IsMulCommutative R]
    (t : G) (htR : t ∈ R) (htL : t ∉ L) (ht2 : t ^ 2 = 1)
    (z : L) (hzR : (z : G) ∈ R) (hz : orderOf z = 2)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU L 3 p)
    (hfix : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
      IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
      Nat.card F = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      J.form = 1 → StandardFixerCoordinates J)
    (hcyclic : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
      IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
      Nat.card F = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      J.form = !![0,0,1;0,1,0;1,0,0] → CyclicInnerPlacement J) :
    HasInvertedCoordinates L R z p := by
  apply hasInvertedCoordinates_of_abelian_action L R hfaithful hR t htR htL ht2
    z hzR hz hp ho hmodel
  intro F _ _ J hsimple hcard hc hJ
  let := hsimple
  obtain ⟨C, es, ep, hC, hes, hep⟩ :=
    HermitianForm.IdentityGram.exists_identityGram_transport J p hp hcard hc
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup
      (HermitianForm.IdentityGram.identityGram J)) := ep.symm.isSimpleGroup
  exact abelianOuterCoordinateGeometry_of_cyclicInnerPlacement J hp ho hcard hc hJ
    (hfix F (HermitianForm.IdentityGram.identityGram J) inferInstance hcard hc rfl)
    (hcyclic F J inferInstance hcard hc hJ)
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
