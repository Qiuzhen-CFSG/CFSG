module

public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.DimensionThree.Rank
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.DimensionThree.InvolutionCore
public import Theory.GroupTheory.SylowLocalCoreFromCentralizers
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility

/-!
# The local conditions for normalized PSU₃(3)

The actual projective special unitary group over a field of order nine is
strongly quasithin: its root Sylow three-subgroup has order 27 and is
nonabelian, while the group order excludes all other odd prime cubes.

For condition E, every involution centralizer in SU₃(3) has characteristic
two. A central involution in the two-core of a Sylow-containing two-local
reduces its core bound to this centralizer calculation. The canonical map
SU₃(3) → PSU₃(3) is an isomorphism, since its scalar kernel has exponent
three and lies in the field's unit group of order eight. Transport gives
the bound for the actual projective image and every Sylow two-subgroup.

This proves both requested source clauses without QT, K, E, simplicity,
noncommutativity, or local-classification premises. The identity-Gram
hypothesis is retained for the centralizer calculation.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, repeated as
Theorem 0.1.1(4), printed p.482, with condition E on printed pp.3 and 481.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryThree
open BenderSuzuki.MatrixGroups

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

private instance : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

/-- The normalized actual projective group PSU₃(3) has even characteristic. -/
public theorem evenCharacteristic (hF : Nat.card F = 3 ^ 2)
    (hJ : J.form = 1) (hc : ∀ x, J.conj x = x ^ 3) :
    IsEvenCharacteristic (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hSU : IsEvenCharacteristic J.specialSubgroup := by
    intro T M hM hTM
    exact Theory.GroupTheory.sylow_twoLocal_centralizer_pCore_le_of_characteristic_centralizers
      (special_involutionCentralizer_twoCore J hF hJ hc) T M hM.1 hTM
  exact hSU.of_equiv (J.specialProjectiveEquivOfCardNine hF)

/-- In every maximal two-local containing any Sylow two-subgroup, the intrinsic
two-core contains its centralizer in that local subgroup. -/
public theorem maximalTwoLocal_twoCore (hF : Nat.card F = 3 ^ 2)
    (hJ : J.form = 1) (hc : ∀ x, J.conj x = x ^ 3)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
  evenCharacteristic J hF hJ hc T M hM hTM

/-- Both local clauses of the PSU₃(3) converse, for the actual image in PGL. -/
public theorem local_conditions (hF : Nat.card F = 3 ^ 2)
    (hJ : J.form = 1) (hc : ∀ x, J.conj x = x ^ 3) :
    (∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsTwoLocal M →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p M ≤ 2) ∧
    (∀ T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsMaximalTwoLocal M →
        (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ M →
          Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :=
  ⟨fun M hM _ hp ho => twoLocal_primeRank_le_two J hF hc M hM hp ho,
    evenCharacteristic J hF hJ hc⟩

end CFSG.Quasithin.MainConverse.UnitaryThree
