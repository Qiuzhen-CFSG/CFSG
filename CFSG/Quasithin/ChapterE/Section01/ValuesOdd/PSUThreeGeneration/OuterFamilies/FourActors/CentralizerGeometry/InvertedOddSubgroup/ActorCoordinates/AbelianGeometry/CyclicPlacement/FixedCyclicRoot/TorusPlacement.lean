module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.FixedCyclicRoot.Setup
public import Theory.SpecificGroups.SU3.FixedCyclicTorusPlacement
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Fixed cyclic two-groups in the literal split torus

The fixed field has order p. In the entrywise fixed special-unitary group,
the diagonal torus together with its Weyl coset has order 2(p-1), hence odd
index when p is 1 modulo four. Sylow conjugacy places the given cyclic
two-group in this subgroup, and order greater than two excludes the Weyl
coset. Projectivization preserves the fixed conjugator and the exact torus
parameter used by `FixedCyclicRoot`.

This discharges `FixedCyclicTorusPlacement`; the root-coordinate and marked
involution consequences are assembled by its existing parent consumer.
Source: Aschbacher--Smith E.1.14(7), printed p.214, and A.3.21(a)--(b),
printed p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
variable {F : Type} [Field F] [Finite F]

/-- A larger fixed cyclic two-group has a fixed conjugator into the original
fixed-field torus. No root action or involution-placement hypothesis is needed. -/
theorem fixedCyclicTorusPlacement
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ a, J.conj a = a ^ p) :
    FixedCyclicTorusPlacement J hJ := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card (FixedBy.subfield F J.conj) = p := by
    change Nat.card {a : F // J.conj a = a} = p
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hc)
  intro γ hγ x hx hx2 hlarge
  exact HermitianForm.FixedCyclicTorusPlacement.exists_fixed_torus_conjugator
    J hJ hγ hp.one_lt ho hmod hfixed x hx hx2 hlarge

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
