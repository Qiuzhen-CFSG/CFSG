module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.SylowEightRigidity.AmbientComparison
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.SylowEightRigidity.TwoPartCertificate
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.SylowEightRigidity.ProfileCertificates

/-!
# Characteristic normal elementary eights in max4 Sylow subgroups

A normal eight in a finite two-group lies in its third upper central term.
An automorphism permutes the normal elementary eights and preserves the order
of the third lower-central term of each centralizer. A complete three-entry
catalogue with orders 128, 1024, and 512 therefore fixes each entry.

The reference group is the existing actual max1 matrix two-subgroup. An actual
isomorphism from one local max4 Sylow transports this argument, and local Sylow
conjugacy handles every max4 Sylow. The proved two-part certificate supplies
the model comparison, and the checked presentation realization supplies the
complete catalogue and centralizer orders. The final theorem discharges both
concrete inputs and proves the unconditional characteristicity contract.

Source context: Kleidman--Wilson (1988), pp.484--510; Aschbacher--Smith,
`refs/quasithin.pdf`, printed p.511/PDF p.528, citing Aschbacher (1986).
The source context is motivation; the finite certificate obligations are those
published in `SylowEightRigidity.Certificates`.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

open Subgroup

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The general p-group bound applied to the literal max4 local Sylow.
No elementary-abelian assumption is needed for this containment. -/
theorem max4_normal_eight_le_third_center
    (P : Sylow 2 Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    (A : Subgroup P) [A.Normal] (hcard : Nat.card A = 8) :
    A ≤ Subgroup.upperCentralSeries P 3 :=
  Subgroup.le_upperCentralSeries_of_card_eq_prime_pow P.isPGroup' A hcard

private theorem normalEightCentralizerOrder_injective :
    Function.Injective normalEightCentralizerOrder := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [normalEightCentralizerOrder] at *

/-- The complete three-entry centralizer calculation implies reference-group rigidity. -/
theorem sylowEightModel_characteristic_of_certificates
    (hcert : Max4SylowEightCentralizerCertificates)
    (A : Subgroup SylowEightModel) [A.Normal] [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 8) : A.Characteristic := by
  obtain ⟨family, hcover, hcards⟩ := hcert
  apply Subgroup.characteristic_of_centralizer_profile
    Janko4.OuterReduction.OddIndex.twoSubgroup_isPGroup (n := 3) (k := 2)
    family hcover ?_ A hcard
  intro i j h
  apply normalEightCentralizerOrder_injective
  simpa only [hcards] using h

/-- Actual model comparison and finite certificates imply the exact local contract. -/
theorem max4SylowElementaryEightCharacteristic_of_certificates
    (hcomparison : Max4SylowEightModelComparison)
    (hcert : Max4SylowEightCentralizerCertificates) :
    Max4SylowElementaryEightCharacteristic := by
  obtain ⟨P₀, ⟨e₀⟩⟩ := hcomparison
  intro P A hnormal helementary hcard
  let : A.Normal := hnormal
  let : IsElementaryAbelian 2 A := helementary
  let e : P ≃* SylowEightModel := (P.equiv P₀).trans e₀
  have : (A.map e.toMonoidHom).Normal := Subgroup.Normal.map hnormal e.toMonoidHom e.surjective
  have : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hc : (A.map e.toMonoidHom).Characteristic :=
    sylowEightModel_characteristic_of_certificates hcert _ (by
      rw [Subgroup.card_map_of_injective e.injective, hcard])
  exact Subgroup.characteristic_of_map_mulEquiv e A hc

/-- The conditional route from a literal two-part lower bound and the
three-entry finite calculation, retained with its original interface. -/
theorem max4SylowElementaryEightCharacteristic_of_twoPart
    (horder : 2 ^ 21 ∣ Nat.card Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    (hcert : Max4SylowEightCentralizerCertificates) :
    Max4SylowElementaryEightCharacteristic :=
  max4SylowElementaryEightCharacteristic_of_certificates
    (max4SylowEightModelComparison_of_twoPart horder) hcert

/-- Every normal elementary subgroup of order eight in an intrinsic Sylow
two-subgroup of literal max4 is characteristic. The actual model comparison
and all finite catalogue and centralizer certificates are discharged. -/
theorem max4SylowElementaryEightCharacteristic : Max4SylowElementaryEightCharacteristic :=
  max4SylowElementaryEightCharacteristic_of_certificates
    max4SylowEightModelComparison max4SylowEightCentralizerCertificates

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
