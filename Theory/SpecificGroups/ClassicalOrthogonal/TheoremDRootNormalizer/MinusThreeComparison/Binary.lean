module
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual.AmbientPerfectness

/-!
# The binary endpoint of the minus-six/unitary-four comparison

Ambient SU₄ perfectness puts the descended exterior image in the literal
full orthogonal commutator even over the binary fixed field. The existing
normal elementary subgroup lies in this image and is nontrivial. Inherited
simplicity of the original projective orthogonal carrier therefore gives
exact image equality. The existing quadratic-coordinate transport and
canonical projective maps produce the comparison for every positive
exponent, including the actual field-of-four Hermitian model at exponent one.

Source: Aschbacher–Smith A.2.18 and Theorem D, printed pp.40 and1078–1079.
No unitary perfectness or orthogonal image-containment premise is assumed.
-/

public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary

variable (n : ℕ) [NeZero n]

/-- The original quadratic-extension unitary carrier is perfect at every positive exponent. -/
theorem su_isPerfect_of_neZero : Group.IsPerfect (SU n) :=
  UnitaryFourPointResidual.AmbientPerfectness.antidiagonal_isPerfect
    (Field n) (conjugation n)
    (Representation.OrthogonalFourMinus.FiniteModel.conjugation_involutive n)
    (Representation.OrthogonalFourMinus.FiniteModel.exists_conjugation_ne n)

/-- The actual exterior image lies in the literal orthogonal commutator, also at exponent one. -/
theorem orthogonalAction_range_le_commutator_of_neZero (hD : Descends n) :
    (orthogonalAction n hD).range ≤ commutator (FullOrthogonal n) := by
  let := su_isPerfect_of_neZero n
  have h := map_derivedSeries_le_derivedSeries (orthogonalAction n hD) 1
  rw [derivedSeries_one,derivedSeries_one,Group.IsPerfect.commutator_eq_top,
    ← MonoidHom.range_eq_map] at h
  exact h

/-- Inherited simplicity exhausts the commutator by the actual unitary exterior image. -/
theorem orthogonalAction_range_eq_commutator_of_neZero (hD : Descends n)
    [IsSimpleGroup (Omega n)] :
    (orthogonalAction n hD).range = commutator (FullOrthogonal n) := by
  have hER := Normality.elementary_le_range n hD
  have hRO := orthogonalAction_range_le_commutator_of_neZero n hD
  have hN := Normality.elementary_normal n
  have hs : IsSimpleGroup ↥(commutator (FullOrthogonal n)) := inferInstance
  have hE : elementarySubgroup (form n) = commutator (FullOrthogonal n) :=
    ((Subgroup.isSimpleGroup_iff.mp hs).2 _ (hER.trans hRO)
      (hN.subgroupOf _)).resolve_left (Normality.elementary_ne_bot n hD)
  exact le_antisymm hRO (hE ▸ hER)

variable {F : Type} [_root_.Field F] [Finite F]

omit [NeZero n] in
/-- The field-and-form comparison for every positive fixed-field exponent. -/
theorem exists_comparison_pos (hn : 0 < n) (hcard : Nat.card F = 2^n)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    ∃ (E : Type) (_ : _root_.Field E) (_ : Finite E) (J : HermitianForm 4 E),
      Nat.card E = (2^n)^2 ∧ (∀ x, J.conj x = x^(2^n)) ∧
        Nonempty (ClassicalGroup.POmegaMinus 3 F ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : NeZero n := ⟨by omega⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [← Nat.card_eq_fintype_card] using hcard)
  let : IsSimpleGroup (Omega n) := omega_isSimple_of_fullEquiv n (fullOrthogonalEquiv n hcard)
  exact exists_comparison_of_descent_range_transport n hcard (descends n)
    (orthogonalAction_range_eq_commutator_of_neZero n (descends n)) (fullOrthogonalEquiv n hcard)

omit [NeZero n] in
/-- The missing binary minus-six endpoint, with its genuine field-of-four Hermitian model. -/
theorem exists_comparison_binary (hcard : Nat.card F = 2)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    ∃ (E : Type) (_ : _root_.Field E) (_ : Finite E) (J : HermitianForm 4 E),
      Nat.card E = 4 ∧ (∀ x, J.conj x = x^2) ∧
        Nonempty (ClassicalGroup.POmegaMinus 3 F ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  simpa only [pow_one,show (2:ℕ)^2 = 4 from rfl] using
    exists_comparison_pos 1 (by decide) (by simpa only [pow_one] using hcard)

end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
