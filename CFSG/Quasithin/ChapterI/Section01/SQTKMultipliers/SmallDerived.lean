module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.AlternatingLinear
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv.MatrixHom

/-!
# Small model endpoints for the I.1.3 assembly

The nonsimple unitary endpoint PSU₃(2) is excluded by its proved solvability,
using the actual Hermitian form and fixed-field conventions. This removes an
unnecessary source premise from the degree-three field restriction.
Fong recognition identifies the literal G₂(2) commutator with PSU₃(3),
including the genuine coefficient field of order nine and cube conjugation.

For the literal commutator ²G₂(3)′, the deleted-module matrix homomorphism is
already constructed. Its outstanding nine-point projective identification
then gives an actual PSL₂(8) equivalence, so the completed even degree-two
kernel theorem proves vanishing. The displayed conditional application
does not supply that outstanding projective identification.

Source: GLS3 §2.2 (A₁(8) ≅ ²G₂(3)′) and Aschbacher--Smith I.1.3, p.407.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers
open PerfectCentralCovering
open scoped MatrixGroups
universe u
variable {S : Type u} [Group S] [Finite S] [Group.IsPerfect S]

omit [Finite S] in
/-- Perfect simple source groups cannot be the solvable unitary endpoint. -/
theorem not_psu3_two [IsSimpleGroup S] : ¬ ClassicalGroup.IsPSU S 3 2 := by
  rintro ⟨F, hF, hfin, J, hc, hj, ⟨e⟩⟩
  let := hF
  let := hfin
  let : Group.IsSolvable (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.projective_isSolvable J hc hj
  let : Group.IsSolvable S :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.IsPerfect.not_isSolvable S inferInstance

omit [Finite S] [Group.IsPerfect S] in
/-- Fong's proved comparison supplies the actual unitary source-model witness
for G₂(2)′; the coefficient field and Frobenius convention are explicit. -/
theorem g2Derived_isPSU_three (e : S ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ClassicalGroup.IsPSU S 3 3 := by
  refine ⟨GaloisField 3 (2 * 1), inferInstance, inferInstance,
    ABG.unitaryForm 3 3 1 (by decide), ?_, ?_, ?_⟩
  · simpa using GaloisField.card 3 (2 * 1) (by decide)
  · intro x
    simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]
  · exact ⟨e.trans Atlas.G2.nonempty_commutator_binary_equiv_psu3.some⟩

/-- The exact remaining projective identification discharges the small Ree
canonical-kernel clause, using the already proved literal matrix map. -/
theorem multiplier_reeDerived_of_projectiveEquiv
    (ep : Atlas.ReeG2.TernaryDerived.PermutationModel ≃* PSL(2, GaloisField 2 3))
    (e : S ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0)) :
    Subsingleton (schurMultiplier S) := by
  apply multiplier_even_psl2 (q := 8) (by decide) (by decide)
  refine ⟨GaloisField 2 3, inferInstance, inferInstance, ?_, ?_⟩
  · simpa using GaloisField.card 2 3 (by decide)
  · exact ⟨e.trans (Atlas.ReeG2.TernaryDerived.equivOfPermutationModel ep
      Atlas.ReeG2.TernaryDerived.toRee Atlas.ReeG2.TernaryDerived.toRee_ne_one)⟩

end CFSG.Quasithin.ChapterI.SQTKMultipliers
