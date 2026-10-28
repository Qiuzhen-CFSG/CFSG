module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.GraphComparison
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Normalization of odd-prime projective unitary outer involutions

First change an arbitrary Hermitian Gram matrix to the antidiagonal matrix,
using an actual conjugation equivalence between the images in PGL. On that
model, the prime-square field calculation identifies the field component of
any semilinear outer involution with the stored Hermitian conjugation. A
projective unitary coboundary then gives the required conjugating equivalence.

The theorem `normalized_outer` discharges both structural inputs of the
conditional reduction below. `Coverage` supplies a semilinear formula for
every automorphism of the actual projective image, using its inherited
simplicity. `Descent` proves that an involutory unitary twist is a projective
coboundary, including characteristic three and the scalar ambiguity in
odd-field symmetric-form similarity. No perfectness hypothesis is needed.

This is the precise normalization used by
`OddPrimeSylow.inner_of_normalized_outer_and_orthogonal_bound`, for
`p % 8 = 3`, retaining `p = 3`.
Source: Aschbacher–Smith F.6.18(10)–(11), printed pp.309–310, and the component
argument of 15.4.18, pp.1162–1163; GLS3, Theorem 2.5.12 and Section 2.7.
-/

open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter

variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- A projective matrix coboundary removes a unitary twist by an actual group
equivalence. This result assumes precisely the displayed matrix equality. -/
public theorem entrywise_congr_of_coboundary
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u v : J.unitarySubgroup)
    (huv : ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk
      (v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹)) :
    J.IsEntrywiseConjugation
      (MulAut.congr (J.unitaryConj v).symm (J.unitaryConj u * γ)) := by
  have h := J.congr_unitaryConj_of_projective_coboundary hγ u v huv
  rw [← h]
  have he : MulAut.congr (J.unitaryConj v).symm
      (MulAut.congr (J.unitaryConj v) γ) = γ := by
    ext x
    simp [MulAut.congr]
  rwa [he]

/-- Conditional normalization with the two structural inputs displayed.
Both concern only the fixed antidiagonal model; arbitrary-form transport and
identification of the field component are proved here. The theorem
`normalized_outer` below supplies both inputs. -/
public theorem normalized_outer_of_semilinear_and_descent [Finite E]
    {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (hcoverage : ∀ a : MulAut
        (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)),
      a ^ 2 = 1 → (¬ ∃ k, a = MulAut.conj k) →
      ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasUnitarySemilinearForm a σ)
    (hdescent : ∀ u : (FormTransport.standardForm J).unitarySubgroup,
      ((FormTransport.standardForm J).unitaryConj u *
        entrywiseProjectiveAut (FormTransport.standardForm J) rfl) ^ 2 = 1 →
      ∃ v : (FormTransport.standardForm J).unitarySubgroup,
        ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk
          (v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ k, a = MulAut.conj k) :
    ∃ (J₀ : HermitianForm 3 E)
      (e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup J₀),
      J₀.conj = J.conj ∧ J₀.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        J₀.IsEntrywiseConjugation (MulAut.congr e a) := by
  let J₀ := FormTransport.standardForm J
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J p hcard hfixed
  let b := MulAut.congr e a
  have hb : b ^ 2 = 1 := by
    dsimp only [b]
    rw [← map_pow, ha, map_one]
  have hbouter : ¬ ∃ k, b = MulAut.conj k :=
    fun h => houter ((MulAut.congr_inner_iff e a).mp h)
  let γ := entrywiseProjectiveAut J₀ rfl
  have hγ : J₀.IsEntrywiseConjugation γ :=
    entrywiseProjectiveAut_isEntrywiseConjugation J₀ rfl
  obtain ⟨u, hu⟩ := outer_twist_of_semilinear J₀ hp hcard hfixed hγ b hb hbouter
    (hcoverage b hb hbouter)
  obtain ⟨v, hv⟩ := hdescent u (by rw [← hu]; exact hb)
  refine ⟨J₀, e.trans (J₀.unitaryConj v).symm, rfl, rfl, ?_⟩
  have hgraph := entrywise_congr_of_coboundary J₀ hγ u v hv
  rw [← hu] at hgraph
  have he : MulAut.congr (e.trans (J₀.unitaryConj v).symm) a =
      MulAut.congr (J₀.unitaryConj v).symm b := by
    ext x
    rfl
  rwa [he]

/-- Every outer involution of the actual projective SU₃ image over a field of
order `p²`, with fixed-field order `p ≡ 3 (mod 8)`, becomes entrywise Hermitian
conjugation under an actual multiplicative equivalence to the antidiagonal
model. The original field involution is retained. There is no semilinearity,
descent or normalization premise, and the case `p = 3` is included. -/
public theorem normalized_outer [Finite E]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ k, a = MulAut.conj k) :
    ∃ (J₀ : HermitianForm 3 E)
      (e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup J₀),
      J₀.conj = J.conj ∧ J₀.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        J₀.IsEntrywiseConjugation (MulAut.congr e a) := by
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J p hcard hfixed
  let : IsSimpleGroup
      (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) :=
    e.symm.isSimpleGroup
  exact normalized_outer_of_semilinear_and_descent J hp hcard hfixed
    (fun b _ _ => Coverage.semilinear_coverage
      (FormTransport.standardForm J) rfl hp hp8 hcard hfixed b)
    (fun u hu => Descent.projective_descent
      (FormTransport.standardForm J) hp hp8 hcard hfixed rfl
      (entrywiseProjectiveAut_isEntrywiseConjugation (FormTransport.standardForm J) rfl)
      u hu) a ha houter

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
