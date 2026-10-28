module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model

/-!
# Model inputs for the odd-prime PSU₃ generation argument

The field has order p² and its stored involution is the p-power map.
An orthonormal basis gives an actual equivalence of projective images with
the identity-form model. Perfectness of the original projective image then
supplies the nonabelianness required by the simple-socle E₂ argument.
Both results include p = 3 and retain the scalar kernel of SU₃ → PSU₃.

Source: Aschbacher--Smith, E.1.14(7), printed p.214, and A.2.3(2),
printed p.33. The model results use Huppert II.10.4 and II.10.13.
These are inputs to generation, not a proof of the upper bound.
-/

public section

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration

variable {L : Type*} [Group L] {p : ℕ}

/-- Normalize the Gram matrix through a genuine equivalence in PGL, while
preserving the field and the specified Frobenius involution. -/
theorem exists_identity_model (hp : p.Prime)
    (hmodel : ClassicalGroup.IsPSU L 3 p) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F),
      J.form = 1 ∧ Nat.card F = p ^ 2 ∧ (∀ x, J.conj x = x ^ p) ∧
        Nonempty (L ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨C, hC⟩ := J.exists_orthonormal_basis_of_prime_frobenius hc hcard
  exact ⟨F, inferInstance, inferInstance, identityForm J.conj J.conj_involutive,
    rfl, hcard, hc, ⟨e.trans (projectiveBasisEquiv J C hC)⟩⟩

/-- Perfectness belongs to the projective group specified by the source model. -/
theorem isPerfect_of_model (hp : p.Prime) (hodd : Odd p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) : Group.IsPerfect L := by
  obtain ⟨F, _, _, J, _, hcard, hc, ⟨e⟩⟩ := exists_identity_model hp hmodel
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (by
    intro h
    exact hodd.not_two_dvd_nat (h ▸ dvd_rfl))
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    J.projective_isPerfect_of_fixed_card hp2 hcard
      (J.card_fixed_of_prime_frobenius hc)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- This discharges the nonabelian premise of the shared simple-socle E₂
construction; source simplicity already supplies nontriviality. -/
theorem nonabelian_of_model [Nontrivial L] (hp : p.Prime) (hodd : Odd p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) : ¬ IsMulCommutative L := by
  let := isPerfect_of_model hp hodd hmodel
  exact Group.IsPerfect.not_isMulCommutative L

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
