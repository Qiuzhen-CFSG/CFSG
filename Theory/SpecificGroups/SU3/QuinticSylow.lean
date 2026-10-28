module
public import Theory.SpecificGroups.SU3.OddPrimeRootConfiguration

/-!
# Sylow five-groups in the concrete PSU₃(5) model

The Hermitian root configuration gives an extraspecial subgroup of order
125 for the original form. The projective order formula makes its index
1008, prime to five, so it is Sylow. Sylow conjugacy transports the group
structure and order to every supplied Sylow five-subgroup.

This supplies only the Sylow structure in Aschbacher--Smith, original
4.3.2, printed p.618. Placement of the center in the specified local
subgroup remains a separate geometric assertion. The matrix input is
Huppert, Endliche Gruppen I, II.10.12.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.QuinticSylow
open OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F] [Finite F]

/-- The Sylow five-groups of the actual PSU₃(5) model are extraspecial of order 125. -/
theorem extraspecial_card (J : HermitianForm 3 F)
    (hF : Nat.card F = 5 ^ 2) (hc : ∀ x, J.conj x = x ^ 5)
    (S : Sylow 5 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    IsExtraspecial 5 S ∧ Nat.card S = 5 ^ 3 := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hf : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
      (by simpa only [pow_one] using hc)
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J 5 hF hf
  obtain ⟨_, _, _, _, _, _, _, _, horder, _⟩ :=
    huppert_II_10_12 (FormTransport.standardForm J) 5 hF hf rfl
  have hcard : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 126000 := by
    rw [Nat.card_congr e.toEquiv, horder]
    norm_num
  obtain ⟨P, hP, hPc, _⟩ := hasRationalExtraspecialSubgroup_of_prime J
    (by decide : Nat.Prime 5) hF hc
  let : IsExtraspecial 5 P := hP
  have hidx : P.index = 1008 := by
    have hh := P.card_mul_index
    rw [hPc, hcard] at hh
    omega
  let R : Sylow 5 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (IsExtraspecial.isPGroup 5 P).toSylow (hidx ▸ by decide)
  let d : R ≃* S := R.equiv S
  exact ⟨IsExtraspecial.of_mulEquiv d hP, (Nat.card_congr d.toEquiv).symm.trans hPc⟩

end BenderSuzuki.MatrixGroups.HermitianForm.QuinticSylow
