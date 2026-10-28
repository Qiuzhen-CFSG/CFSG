module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality.NormVectors
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality.FirstColumn
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Order of the special unitary group in dimension four

Over a field of order q² with prime q > 3 and Frobenius conjugation, the
actual special unitary matrix group has order
`q⁶ * (q²-1) * (q³+1) * (q⁴-1)` for every nondegenerate Hermitian form.

For the identity form, count first-column fibers in dimensions three and
four using transitivity on norm-one vectors and the actual SU stabilizer
in one lower dimension. The base SU₂ is isomorphic to SL₂ over the fixed
field of order q. An orthonormal basis then transports the count to the
original stored form. No projective-group order or covering bound is assumed.

Source application: the block-pair index calculation supporting
Aschbacher–Smith I.1.4(3), printed p.408 of `refs/quasithin.pdf`, and GLS3 §6.1.
The theorem's equality supplies the ambient-count premise of
`TwoPrimary.odd_index_blockModel_of_card_dvd` without importing that higher
consumer here.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)

private theorem card_special_two [Finite F] {q : ℕ} (hq : IsPrimePow q) (ho : Odd q)
    (hc : Nat.card F = q^2) (hj : ∀ x, σ x = x^q) :
    Nat.card (form σ hσ 2).specialSubgroup = q * (q^2-1) := by
  obtain ⟨e⟩ := nonempty_specialTwoEquiv_odd σ hσ hq ho hc hj
  have hk : Nat.card (FixedBy.subfield F σ) = q :=
    (form σ hσ 2).fixed_card_prime_power hq hc hj
  rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, hk]

private theorem card_special_identity_four [Finite F] {q : ℕ} [Fact q.Prime]
    (hq : 3 < q) (hc : Nat.card F = q^2) (hj : ∀ x, σ x = x^q) :
    Nat.card (form σ hσ 4).specialSubgroup =
      q^6 * (q^2-1) * (q^3+1) * (q^4-1) := by
  have hp : IsPrimePow q := (isPrimePow_nat_iff _).mpr
    ⟨q, 1, Fact.out, by decide, by simp⟩
  have ho : Odd q := (Fact.out : q.Prime).odd_of_ne_two (by omega)
  have h3 := card_special_succ σ hσ (r := q) (e := 1) (by omega) (by decide)
    (by simpa using hc) (by simpa using hj) 0
  have h4 := card_special_succ σ hσ (r := q) (e := 1) (by omega) (by decide)
    (by simpa using hc) (by simpa using hj) 1
  rw [h4, h3, card_special_two σ hσ hp ho hc hj,
    card_norm_one_three σ hσ hp hc hj, card_norm_one_four σ hσ hp hc hj]
  ring

/-- The exact order of the actual special unitary group, with the original form. -/
theorem card_specialSubgroup [Finite F] (J : HermitianForm 4 F)
    {q : ℕ} [Fact q.Prime] (hq : 3 < q) (hc : Nat.card F = q^2)
    (hj : ∀ x, J.conj x = x^q) :
    Nat.card J.specialSubgroup = q^6 * (q^2-1) * (q^3+1) * (q^4-1) := by
  obtain ⟨C, e, ep, hC, he, hep⟩ :=
    HermitianForm.IdentityGram.exists_identityGram_transport J q Fact.out hc hj
  rw [Nat.card_congr e.toEquiv]
  exact card_special_identity_four J.conj J.conj_involutive hq hc hj

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality
