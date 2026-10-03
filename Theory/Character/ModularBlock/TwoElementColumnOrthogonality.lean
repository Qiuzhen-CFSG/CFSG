module

public import Theory.Character.ModularBlock.BrauerConjugationTrace
public import Theory.Character.ModularBlock.MixedConjugationTrace

/-!
# Off-diagonal principal-block columns at two-elements

For two-elements `a`, `b` that are not conjugate, the permutation
`x ↦ a⁻¹ * x * b` has two-power order and no fixed points. Right multiplication
by the integral principal selector is an idempotent commuting with this
permutation. The integral permutation-summand trace theorem makes its projected
trace zero. Scalar extension and the ordinary mixed-trace formula identify
this with the inner product of the two actual principal-block columns.

This includes identity versus any nonidentity two-element. No assertion about
local centralizers or any decomposition matrix is needed.

Source: Brauer, *Some applications of the theory of blocks of characters of
finite groups. II* (1964), §V Lemmas 3–4, invoking §II (2.6), (2.8).
-/

public section
open scoped BigOperators
noncomputable section
open ModularBlock.PrincipalBlockConstruction ModularBlock.BrauerBlockReduction
open ModularBlock.BrauerConjugationTrace ModularBlock.MixedConjugationTrace
attribute [local instance] Fintype.ofFinite

namespace ModularBlock.TwoElementColumnOrthogonality
variable {G R : Type*} [Group G] [Finite G] [CommRing R]
private def leftRightPerm (a b : G) : Equiv.Perm G :=
  (Equiv.mulRight b).trans (Equiv.mulLeft a⁻¹)
omit [Finite G] in
@[simp] private theorem leftRightPerm_apply (a b x : G) :
    leftRightPerm a b x = a⁻¹ * x * b := by simp [leftRightPerm, mul_assoc]
omit [Finite G] in
private theorem leftRightPerm_pow (a b : G) (m : ℕ) :
    leftRightPerm a b ^ m = leftRightPerm (a ^ m) (b ^ m) := by
  induction m with
  | zero => ext x; simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext x
    simp only [Equiv.Perm.mul_apply, leftRightPerm_apply, pow_succ, mul_inv_rev]
    rw [← inv_pow]
    group

/-- Nonconjugate two-elements have orthogonal columns in the prescribed
principal two-block, including when one element is the identity. -/
theorem principalBlock_column_orthogonal (d : PrincipalCongruenceBlockData G) (a b : G)
    (ha : ∃ n : ℕ, a ^ (2^n) = 1) (hb : ∃ n : ℕ, b ^ (2^n) = 1)
    (hab : ¬ IsConj a b) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk a) * star (d.chi i (ConjClasses.mk b)) = 0 := by
  classical
  let : Field (principalResidueField d) := Ideal.Quotient.field d.primeIdeal
  let e := ModularBlock.BlockOrthogonality.localizedPrincipalBlockElement d
  let σ := leftRightPerm a b
  have hfree (x : G) : σ x ≠ x := by
    intro h
    apply hab
    have hh : a * x = x * b := by
      simp only [σ, leftRightPerm_apply] at h
      have := congrArg (fun z => a * z) h
      simpa [mul_assoc] using this.symm
    exact isConj_iff.mpr ⟨x⁻¹, by simp only [inv_inv, mul_assoc, hh, inv_mul_cancel_left]⟩
  let : IsEmpty {x // σ x = x} := ⟨fun x => hfree x x.property⟩
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  have hσ : σ ^ (2 ^ (m+n)) = 1 := by
    rw [leftRightPerm_pow]
    have ha' : a ^ (2 ^ (m+n)) = 1 := by rw [pow_add, pow_mul, hm, one_pow]
    have hb' : b ^ (2 ^ (m+n)) = 1 := by rw [Nat.add_comm m n, pow_add, pow_mul, hn, one_pow]
    rw [ha', hb']
    ext x
    simp
  have hcomm : Commute (σ.permMatrix (Localization.AtPrime d.primeIdeal)) (rightMatrix e) := by
    rw [Matrix.commute_permMatrix_iff_entries]
    intro i j
    simp only [rightMatrix, σ, leftRightPerm_apply]
    have hh : (a⁻¹ * j * b)⁻¹ * (a⁻¹ * i * b) = b⁻¹ * (j⁻¹ * i) * (b⁻¹)⁻¹ := by group
    rw [hh]
    exact ModularBlock.CentralIdempotentSupport.coeff_conj_eq_of_mem_center e
      (ModularBlock.BlockOrthogonality.localizedPrincipalBlockElement_mem_center d) _ _
  have hsurj : Function.Surjective (localizationToResidue d) := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap _ (Localization.AtPrime d.primeIdeal) c,
      localizationToResidue_algebraMap d c⟩
  have hf (r : Localization.AtPrime d.primeIdeal) (hr : localizationToResidue d r ≠ 0) : IsUnit r := by
    by_contra h
    exact hr ((ModularBlock.BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d r).mpr h)
  have ht := Matrix.trace_permMatrix_mul_eq_trace_fixed_lift
    (localizationToResidue d) hsurj hf σ hσ (rightMatrix e)
    (rightMatrix_isIdempotent e (ModularBlock.BlockOrthogonality.localizedPrincipalBlockElement_isIdempotent d))
    hcomm (0 : Matrix {x // σ x = x} {x // σ x = x} _) (by simp [IsIdempotentElem])
    (by ext x; exact isEmptyElim x)
  have hz : (∑ x : G, e.coeff (x⁻¹ * a⁻¹ * x * b)) = 0 := by
    simpa [PEquiv.toMatrix_toPEquiv_mul, Matrix.trace, Matrix.diag, rightMatrix, σ,
      mul_assoc] using ht
  have hc := congrArg (ModularBlock.IsotypicLattice.localizationToComplex d) hz
  rw [map_sum, map_zero] at hc
  rw [← principalBlock_leftRight_trace, trace_projectedLeftRight]
  rw [← ModularBlock.BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
    d (ModularBlock.IsotypicLattice.localizationToComplex d)
    (ModularBlock.IsotypicLattice.localizationToComplex_algebraMap d)]
  simpa only [MonoidAlgebra.coeff_mapRingHom] using hc
end ModularBlock.TwoElementColumnOrthogonality
