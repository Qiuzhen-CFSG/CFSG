module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.DimensionThree
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.DimensionFour.Assembly
public import CFSG.Quasithin.MainConverse.Transport
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence

/-!
# The odd unitary converse in dimensions three and four

PSU₃(3) and PSU₄(3) are quasithin and have even characteristic. The field has
order nine, and the stored conjugation is x ↦ x³. The model predicate permits
every nondegenerate Hermitian form. In dimension three, an actual projective
basis-change equivalence reduces to the identity Gram matrix, where the local
rank and involution-centralizer calculations apply. In dimension four, the
completed local calculations already include arbitrary-form transport through
an equivalence of the actual images in PGL.

Transport to the given group preserves the odd-prime ranks of its two-locals
and the intrinsic two-cores of its Sylow-containing maximal two-locals. All
local premises have been discharged; simplicity and noncommutativity are not
needed for these two conclusions.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 of
`refs/quasithin.pdf`, repeated as Theorem 0.1.1(4), printed p.482.
The QT and E conditions are defined on printed pp.3–4 and 481–482.
-/

namespace ClassicalGroup

open BenderSuzuki.MatrixGroups HermitianForm.IdentityGram

/-- A prime fixed-field unitary model can always be realized with identity Gram
matrix. This is an actual projective isomorphism, obtained from a basis change;
no local subgroup or classification hypotheses are required. -/
public theorem IsPSU.exists_identityGram_model
    {G : Type*} [Group G] {n p : ℕ} (h : IsPSU G n p) (hp : p.Prime) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm n F),
      Nat.card F = p ^ 2 ∧ (∀ x, J.conj x = x ^ p) ∧ J.form = 1 ∧
        Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨F, hF, hfinite, J, hcard, hconj, ⟨e⟩⟩ := h
  obtain ⟨_, _, ep, _, _, _⟩ := exists_identityGram_transport J p hp hcard hconj
  exact ⟨F, hF, hfinite, identityGram J, hcard, hconj, rfl, ⟨e.trans ep⟩⟩

end ClassicalGroup

namespace CFSG.Quasithin.MainConverse

open BenderSuzuki.MatrixGroups

/-- The QT and E clauses for PSU₃(3), allowing any nondegenerate Hermitian
form in the model witness. Identity-Gram reduction is an actual isomorphism. -/
public theorem psu3_three_qt_and_evenCharacteristic_of_isPSU
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSU G 3 3) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨F, hfield, hfinite, J, hcard, hconj, hgram, ⟨e⟩⟩ :=
    hG.exists_identityGram_model Nat.prime_three
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv G e.toEquiv
  obtain ⟨hqt, hE⟩ := UnitaryThree.local_conditions J hcard hgram hconj
  exact ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm
    (Theory.GroupTheory.isQuasithin_iff_twoLocal.mpr hqt),
    evenCharacteristic_of_model_equiv e hE⟩

/-- The QT and E clauses for PSU₄(3), retaining the full scalar kernel in the
projective model and transporting from every allowed Hermitian form. -/
public theorem psu4_three_qt_and_evenCharacteristic_of_isPSU
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSU G 4 3) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨F, hfield, hfinite, J, hcard, hconj, ⟨e⟩⟩ := hG
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv G e.toEquiv
  obtain ⟨hqt, hE⟩ := UnitaryFourThree.quasithin_and_evenCharacteristic J hcard hconj
  exact ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm hqt,
    evenCharacteristic_of_model_equiv e hE⟩

/-- Both odd unitary alternatives of the source converse satisfy QT and E.
The parameter three is the fixed-field order, so the matrix field has order nine. -/
public theorem psu_three_four_qt_and_evenCharacteristic_of_isPSU
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : n = 3 ∨ n = 4)
    (hG : ClassicalGroup.IsPSU G n 3) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  rcases hn with rfl | rfl
  · exact psu3_three_qt_and_evenCharacteristic_of_isPSU hG
  · exact psu4_three_qt_and_evenCharacteristic_of_isPSU hG

end CFSG.Quasithin.MainConverse
