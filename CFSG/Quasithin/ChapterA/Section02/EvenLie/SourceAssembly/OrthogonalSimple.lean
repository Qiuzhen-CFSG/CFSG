module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.SymplecticSimple
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.OddComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison

/-!
# Odd orthogonal and nonbinary orthogonal source branches

The odd orthogonal carrier is the actual symplectic central quotient. In
plus type a rank-three root-normalizer torus excludes every simple-range
rank over fields larger than two. In minus type it leaves ranks two and
three; the literal quadratic and exterior comparisons identify these with
PSL2 over the quadratic extension and PSU4 over the original fixed field.
The binary minus-six endpoint remains separate.
Source: Aschbacher--Smith A.2.18, printed p.40; GLS3 §2.7.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G]

private theorem charTwo_of_binary_card {F : Type} [Field F] [Finite F]
    {a : ℕ} (hc : Nat.card F = 2 ^ a) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)

/-- Transport the odd orthogonal input to the genuine symplectic carrier, retaining rank and field. -/
theorem odd_orthogonal_symplectic {r a : ℕ} (hr : 1 ≤ r)
    (iso : ClassicalGroup.IsPOmegaOdd G r (2 ^ a)) :
    ClassicalGroup.IsPSp G r (2 ^ a) := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let : CharP F 2 := charTwo_of_binary_card hc
  exact ⟨F, hF, hfin, hc,
    ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.oddProjectiveEquivPSp (by omega))⟩⟩

variable [Finite G]

/-- The full odd orthogonal Case I follows through the actual symplectic comparison. -/
theorem caseI_orthogonalOdd [IsSimpleGroup G] {K : GroupClass.{u}}
    (ih : TheoremAOnProperSections K G) (hna : ¬ IsMulCommutative G)
    (hG : IsQuasithin G) (hK : IsKGroup K G) {r a : ℕ} (ha : 0 < a)
    (hp : KnownSimple.OrthogonalOddParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaOdd G r (2 ^ a)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) :=
  caseI_symplectic ih hna hG hK ha hp (odd_orthogonal_symplectic hp.2.1 iso)

/-- Larger-field plus models in every simple-range rank violate the original QT hypothesis. -/
theorem caseI_not_orthogonalPlus_nonbinary (hG : IsQuasithin G)
    {r a : ℕ} (ha : 1 < a) (hr : 3 ≤ r)
    (iso : ClassicalGroup.IsPOmegaPlus G r (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let : CharP F 2 := charTwo_of_binary_card hc
  have hq : 2 < Nat.card F := by
    rw [hc]
    exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) ha
  exact ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.not_quasithin_plus hr hq
    (Theory.GroupTheory.isQuasithin_of_equiv e hG)

/-- The remaining larger-field minus aliases supply the exact B/C conclusions. -/
theorem caseI_orthogonalMinus_nonbinary [IsSimpleGroup G] (hG : IsQuasithin G)
    {r a : ℕ} (ha : 1 < a) (hp : KnownSimple.OrthogonalMinusParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaMinus G r (2 ^ a)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hr : r ≤ 3 := by
    by_contra hn
    obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
    let : CharP F 2 := charTwo_of_binary_card hc
    have hq : 2 < Nat.card F := by
      rw [hc]
      exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) ha
    exact ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.not_quasithin_minus hq
      (by omega) (Theory.GroupTheory.isQuasithin_of_equiv e hG)
  have hmin := hp.2
  interval_cases r
  · have hlin : ClassicalGroup.IsPSL G 2 (2 ^ (2 * a)) := by
      obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
      exact ⟨GaloisField 2 (2 * a), inferInstance, inferInstance,
        GaloisField.card 2 (2 * a) (by omega),
        ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.minusTwoEquivPSL F (by omega) hc)⟩⟩
    have hc : IsTheoremCModel G := .bender (.linear (2 * a) (by omega) hlin)
    exact ⟨hc.toTheoremBModel, fun _ => hc⟩
  · have hunitary : ClassicalGroup.IsPSU G 4 (2 ^ a) := by
      obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
      let : IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F) := e.symm.isSimpleGroup
      obtain ⟨E, hE, hfinite, J, hcard, hconj, ⟨f⟩⟩ :=
        ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.exists_comparison a ha hc
      exact ⟨E, hE, hfinite, J, hcard, hconj, ⟨e.trans f⟩⟩
    exact caseI_unitary hG (by omega) ⟨hp.1, by decide, by omega, by omega⟩ hunitary

/-- The odd orthogonal alternative contradicts the actual simultaneous minimal counterexample. -/
theorem not_minimalCounterexample_orthogonalOdd [IsSimpleGroup G] {K : GroupClass.{u}}
    (h : MinimalCounterexample K G) {r a : ℕ} (ha : 0 < a)
    (hp : KnownSimple.OrthogonalOddParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaOdd G r (2 ^ a)) : False :=
  not_minimalCounterexample_symplectic h ha hp (odd_orthogonal_symplectic hp.2.1 iso)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
