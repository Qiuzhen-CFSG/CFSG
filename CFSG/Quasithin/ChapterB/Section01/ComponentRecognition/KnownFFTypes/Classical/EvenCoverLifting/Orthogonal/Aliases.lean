module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.EvenCoverLifting.Descent
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.OddComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Lifting through actual even orthogonal aliases

Projection away from the odd quadratic radical identifies PΩ₂ᵣ₊₁(q) with
PSp₂ᵣ(q). The Hermitian determinant action identifies PΩ₄⁻(q) with PSL₂(q²),
and quadratic descent of the exterior square identifies PΩ₆⁻(q) with PSU₄(q)
for q > 2. Applying the corresponding lifting premise and the inverse of
these actual carrier maps gives the original orthogonal model for the whole
group. The odd row retains both small-parameter exclusions, and the minus-four
row includes q = 2. The binary minus-six comparison is a separate obligation.

The symplectic, linear and unitary lifting premises are intentionally explicit:
the parent even-classical assembly discharges them with the other family
owners. No orthogonal conclusion or carrier comparison is assumed here.
Source: Aschbacher–Smith B.1.13, printed pp.73–74; GLS3 §§2.7 and 6.1.
The imported comparison modules retain their ATLAS attribution.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.EvenOrthogonal
universe u

/-- Every even prime power is a positive power of two. -/
theorem binary_parameter {q : ℕ} (hq : IsPrimePow q) (he : Even q) :
    ∃ n : ℕ, 0 < n ∧ q = 2 ^ n := by
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp hq
  have hd : 2 ∣ p := (by decide : Nat.Prime 2).dvd_of_dvd_pow
    (hpn.symm ▸ even_iff_two_dvd.mp he)
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp hd).symm
  exact ⟨n, hn, by simpa only [hp2] using hpn.symm⟩

private theorem charTwo_of_even_card {F : Type} [Field F] [Finite F]
    {q : ℕ} (he : Even q) (hc : Nat.card F = q) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hc]
  exact Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp he)

/-- The literal odd orthogonal and symplectic models agree over every even field. Both directions use projection away from the polar radical. -/
theorem odd_iff_symplectic {G : Type u} [Group G] {r q : ℕ}
    (hr : 1 ≤ r) (he : Even q) :
    ClassicalGroup.IsPOmegaOdd G r q ↔ ClassicalGroup.IsPSp G r q := by
  constructor
  · rintro ⟨F, hF, hfin, hc, ⟨e⟩⟩
    let : CharP F 2 := charTwo_of_even_card he hc
    exact ⟨F, hF, hfin, hc,
      ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.oddProjectiveEquivPSp
        (by omega))⟩⟩
  · rintro ⟨F, hF, hfin, hc, ⟨e⟩⟩
    let : CharP F 2 := charTwo_of_even_card he hc
    exact ⟨F, hF, hfin, hc,
      ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.oddProjectiveEquivPSp
        (by omega)).symm⟩⟩

/-- The rank-two minus alias has linear field parameter q², including q = 2. The equivalence is the actual Hermitian determinant action. -/
theorem minus_two_isPSL {G : Type u} [Group G] {q : ℕ}
    (hp : KnownSimple.OrthogonalMinusParameters 2 q) (he : Even q)
    (h : ClassicalGroup.IsPOmegaMinus G 2 q) : ClassicalGroup.IsPSL G 2 (q ^ 2) := by
  obtain ⟨n, hn, rfl⟩ := binary_parameter hp.1 he
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  refine ⟨GaloisField 2 (2 * n), inferInstance, inferInstance, ?_,
    ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.minusTwoEquivPSL F hn hc)⟩⟩
  rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, Nat.mul_comm n 2]

variable {L : Type u} [Group L]

/-- The full odd orthogonal catalogue row lifts through the symplectic lifting theorem at exactly the same rank and field parameter. -/
theorem lift_odd (hcore : pCore 2 L = ⊥) {r q : ℕ}
    (hp : KnownSimple.OrthogonalOddParameters r q) (he : Even q)
    (liftPSp : pCore 2 L = ⊥ → KnownSimple.SymplecticParameters r q → Even q →
      ClassicalGroup.IsPSp (L ⧸ center L) r q → ClassicalGroup.IsPSp L r q)
    (h : ClassicalGroup.IsPOmegaOdd (L ⧸ center L) r q) :
    ClassicalGroup.IsPOmegaOdd L r q := by
  apply (odd_iff_symplectic hp.2.1 he).mpr
  exact liftPSp hcore hp he ((odd_iff_symplectic hp.2.1 he).mp h)

/-- Lift the minus-four row through PSL₂(q²), then return to the original coefficient field using finite-field transport and the inverse carrier comparison. -/
theorem lift_minus_two (hcore : pCore 2 L = ⊥) {q : ℕ}
    (hp : KnownSimple.OrthogonalMinusParameters 2 q) (he : Even q)
    (liftPSL : pCore 2 L = ⊥ → KnownSimple.LinearParameters 2 (q ^ 2) → Even (q ^ 2) →
      ClassicalGroup.IsPSL (L ⧸ center L) 2 (q ^ 2) → ClassicalGroup.IsPSL L 2 (q ^ 2))
    (h : ClassicalGroup.IsPOmegaMinus (L ⧸ center L) 2 q) :
    ClassicalGroup.IsPOmegaMinus L 2 q := by
  obtain ⟨n, hn, rfl⟩ := binary_parameter hp.1 he
  have hpar : KnownSimple.LinearParameters 2 ((2 ^ n) ^ 2) := by
    refine ⟨(isPrimePow_nat_iff _).mpr
      ⟨2, n * 2, by decide, by omega, pow_mul 2 n 2⟩, by decide, ?_⟩
    intro _
    have htwo : 2 ≤ 2 ^ n := by
      simpa only [pow_one] using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn)
    nlinarith
  have hl := liftPSL hcore hpar (he.pow_of_ne_zero (by decide))
    (minus_two_isPSL hp he h)
  obtain ⟨K, hK, hfinK, hcK, ⟨a⟩⟩ := hl
  obtain ⟨F, hF, hfin, hc, ⟨_e⟩⟩ := h
  let E := GaloisField 2 (2 * n)
  have hcE : Nat.card E = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, Nat.mul_comm n 2]
  let : Fintype K := Fintype.ofFinite K
  let : Fintype E := Fintype.ofFinite E
  let t : K ≃+* E := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcK.trans hcE.symm)
  exact ⟨F, hF, hfin, hc,
    ⟨(a.trans (Atlas.fieldEquivPSL 2 t)).trans
      (ClassicalOrthogonal.TheoremDRootNormalizer.minusTwoEquivPSL F hn hc).symm⟩⟩

/-- For q > 2, lift the minus-six row through the actual quadratic-descent PSU₄ carrier. Its simplicity is inherited from the source central quotient. The independent unitary lifting premise retains the exact field and form. -/
theorem lift_minus_three [IsQuasisimple L] (hcore : pCore 2 L = ⊥) {q : ℕ}
    (hp : KnownSimple.OrthogonalMinusParameters 3 q) (he : Even q) (hq : q ≠ 2)
    (liftPSU : ∀ (E : Type) [Field E] [Finite E]
      (J : BenderSuzuki.MatrixGroups.HermitianForm 4 E),
      Nat.card E = q ^ 2 → (∀ x, J.conj x = x ^ q) → pCore 2 L = ⊥ →
      (L ⧸ center L ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) →
      Nonempty (L ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    (h : ClassicalGroup.IsPOmegaMinus (L ⧸ center L) 3 q) :
    ClassicalGroup.IsPOmegaMinus L 3 q := by
  obtain ⟨n, hn, rfl⟩ := binary_parameter hp.1 he
  have hn' : 1 < n := by
    by_contra hle
    have : n = 1 := by omega
    exact hq (by simp only [this, pow_one])
  let : NeZero n := ⟨by omega⟩
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F) := e.symm.isSimpleGroup
  let t := ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.projectiveEquiv n hn' hc
  obtain ⟨a⟩ := liftPSU _ _
    (ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.card_field n)
    (ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.unitaryForm_conj n)
    hcore (e.trans t)
  exact ⟨F, hF, hfin, hc, ⟨a.trans t.symm⟩⟩


/-- Whole-group even Lie output for every odd orthogonal catalogue row. -/
theorem evenLie_of_odd (hcore : pCore 2 L = ⊥) {r q : ℕ}
    (hp : KnownSimple.OrthogonalOddParameters r q) (he : Even q)
    (liftPSp : pCore 2 L = ⊥ → KnownSimple.SymplecticParameters r q → Even q →
      ClassicalGroup.IsPSp (L ⧸ center L) r q → ClassicalGroup.IsPSp L r q)
    (h : ClassicalGroup.IsPOmegaOdd (L ⧸ center L) r q) : IsEvenLieGroup L :=
  .classical (.orthogonalOdd r q hp he (lift_odd hcore hp he liftPSp h))

/-- Whole-group even Lie output for the minus-four alias, including q = 2. -/
theorem evenLie_of_minus_two (hcore : pCore 2 L = ⊥) {q : ℕ}
    (hp : KnownSimple.OrthogonalMinusParameters 2 q) (he : Even q)
    (liftPSL : pCore 2 L = ⊥ → KnownSimple.LinearParameters 2 (q ^ 2) → Even (q ^ 2) →
      ClassicalGroup.IsPSL (L ⧸ center L) 2 (q ^ 2) → ClassicalGroup.IsPSL L 2 (q ^ 2))
    (h : ClassicalGroup.IsPOmegaMinus (L ⧸ center L) 2 q) : IsEvenLieGroup L :=
  .classical (.orthogonalMinus 2 q hp he (lift_minus_two hcore hp he liftPSL h))

/-- Whole-group even Lie output for the minus-six alias over q > 2. -/
theorem evenLie_of_minus_three [IsQuasisimple L] (hcore : pCore 2 L = ⊥) {q : ℕ}
    (hp : KnownSimple.OrthogonalMinusParameters 3 q) (he : Even q) (hq : q ≠ 2)
    (liftPSU : ∀ (E : Type) [Field E] [Finite E]
      (J : BenderSuzuki.MatrixGroups.HermitianForm 4 E),
      Nat.card E = q ^ 2 → (∀ x, J.conj x = x ^ q) → pCore 2 L = ⊥ →
      (L ⧸ center L ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) →
      Nonempty (L ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    (h : ClassicalGroup.IsPOmegaMinus (L ⧸ center L) 3 q) : IsEvenLieGroup L :=
  .classical (.orthogonalMinus 3 q hp he (lift_minus_three hcore hp he hq liftPSU h))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.EvenOrthogonal
