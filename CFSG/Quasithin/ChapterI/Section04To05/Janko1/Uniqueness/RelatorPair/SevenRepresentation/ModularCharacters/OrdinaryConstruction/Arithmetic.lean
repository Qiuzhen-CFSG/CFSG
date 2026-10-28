module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryData
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.LinearCombination

/-!
# Numerical realization checks for the ordinary J₁ table

The literal cyclotomic rows have norm one for the specified centralizer
weights, are distinct, and have positive degrees whose squares sum to 175560.
The proofs reduce to fifth-root and nineteenth-root period moments, checked
by polynomial identities against the corresponding geometric sums.

These facts do not establish that the rows are characters. The consumer in
`OrdinaryConstruction` also requires differences of genuine representation
characters and an enumeration of the actual classes of the source group.

The private period table is definitionally the table from `OrdinaryData`.
Its numerical data retains the GPL-3.0-or-later provenance documented there
and in `../Source.md`. Source application: Janko (1966), summarized by
Gorenstein, *Finite Groups*, §16.6, printed p.482.
-/

open scoped BigOperators
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

private theorem star_root_pow {ζ : ℂ} {n k : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : n ≠ 0) (hk : k ≤ n) : star (ζ ^ k) = ζ ^ (n - k) := by
  have hnorm : ‖ζ ^ k‖ = 1 := by rw [norm_pow, hζ.norm'_eq_one hn, one_pow]
  have hp : ζ ^ (n - k) * ζ ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk, hζ.pow_eq_one]
  exact (Complex.inv_eq_conj hnorm).symm.trans (eq_inv_of_mul_eq_one_left hp).symm

private theorem five_periods {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    let a := ζ + ζ ^ 4
    let b := ζ ^ 2 + ζ ^ 3
    a + b = -1 ∧ a * b = -1 ∧ a ^ 2 + b ^ 2 = 3 ∧
      star a = a ∧ star b = b := by
  dsimp only
  have hg := hζ.geom_sum_eq_zero (by decide : 1 < 5)
  norm_num [Finset.sum_range_succ] at hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hg
  · linear_combination (ζ ^ 3 - ζ + 1) * hg
  · linear_combination (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 + 3 * ζ - 3) * hg
  · have hs : star ζ = ζ ^ 4 := by
      simpa using star_root_pow hζ (by decide) (by decide : 1 ≤ 5)
    rw [star_add, hs, star_root_pow hζ (by decide) (by decide : 4 ≤ 5)]
    norm_num
    ring
  · rw [star_add, star_root_pow hζ (by decide) (by decide : 2 ≤ 5),
      star_root_pow hζ (by decide) (by decide : 3 ≤ 5)]
    norm_num
    ring

private theorem nineteen_periods {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 19) :
    let c := ζ + ζ ^ 7 + ζ ^ 8 + ζ ^ 11 + ζ ^ 12 + ζ ^ 18
    let d := ζ ^ 2 + ζ ^ 3 + ζ ^ 5 + ζ ^ 14 + ζ ^ 16 + ζ ^ 17
    let e := ζ ^ 4 + ζ ^ 6 + ζ ^ 9 + ζ ^ 10 + ζ ^ 13 + ζ ^ 15
    c + d + e = -1 ∧ c ^ 2 + d ^ 2 + e ^ 2 = 13 ∧
      c * d + c * e + d * e = -6 ∧ star c = c ∧ star d = d ∧ star e = e := by
  dsimp only
  have hg := hζ.geom_sum_eq_zero (by decide : 1 < 19)
  norm_num [Finset.sum_range_succ] at hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hg
  · linear_combination (ζ ^ 18 - ζ ^ 17 + ζ ^ 16 + ζ ^ 15 - ζ ^ 14 + ζ ^ 13 + 3 * ζ ^ 12 - 3 * ζ ^ 11 + ζ ^ 10 - 3 * ζ ^ 9 + 3 * ζ ^ 8 + ζ ^ 7 - ζ ^ 6 + ζ ^ 5 + ζ ^ 4 - ζ ^ 3 + ζ ^ 2 + 13 * ζ - 13) * hg
  · linear_combination (ζ ^ 17 + ζ ^ 14 - ζ ^ 12 + 2 * ζ ^ 11 + 2 * ζ ^ 9 - ζ ^ 8 + ζ ^ 6 + ζ ^ 3 - 6 * ζ + 6) * hg
  · have hs : star ζ = ζ ^ 18 := by
      simpa using star_root_pow hζ (by decide) (by decide : 1 ≤ 19)
    simp only [star_add, hs]
    rw [star_root_pow hζ (by decide) (by decide : 7 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 8 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 11 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 12 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 18 ≤ 19)]
    norm_num
    ring
  · simp only [star_add]
    rw [star_root_pow hζ (by decide) (by decide : 2 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 3 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 5 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 14 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 16 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 17 ≤ 19)]
    norm_num
    ring
  · simp only [star_add]
    rw [star_root_pow hζ (by decide) (by decide : 4 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 6 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 9 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 10 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 13 ≤ 19),
      star_root_pow hζ (by decide) (by decide : 15 ≤ 19)]
    norm_num
    ring

private def periodValue (a b c d e : ℂ) : Fin 15 → Fin 15 → ℂ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![56, 0, 2, -2*a, -2*b, 0, 0, 0, 0, 1, a, b, -1, -1, -1],
    ![56, 0, 2, -2*b, -2*a, 0, 0, 0, 0, 1, b, a, -1, -1, -1],
    ![76, 4, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 0, 0, 0],
    ![76, -4, 1, 1, 1, -1, -1, 1, 1, -1, 1, 1, 0, 0, 0],
    ![77, 5, -1, 2, 2, -1, 0, 0, 0, 0, -1, -1, 1, 1, 1],
    ![77, -3, 2, a, b, 0, 0, a, b, 0, a, b, 1, 1, 1],
    ![77, -3, 2, b, a, 0, 0, b, a, 0, b, a, 1, 1, 1],
    ![120, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, c, d, e],
    ![120, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, e, c, d],
    ![120, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, d, e, c],
    ![133, 5, 1, -2, -2, -1, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    ![133, -3, -2, -a, -b, 0, 0, a, b, 1, -a, -b, 0, 0, 0],
    ![133, -3, -2, -b, -a, 0, 0, b, a, 1, -b, -a, 0, 0, 0],
    ![209, 1, -1, -1, -1, 1, -1, 1, 1, 0, -1, -1, 0, 0, 0]]

private theorem periodValue_norm (a b c d e : ℂ)
    (h5sq : a ^ 2 + b ^ 2 = 3) (hsq : c ^ 2 + d ^ 2 + e ^ 2 = 13)
    (ha : star a = a) (hb : star b = b) (hc : star c = c)
    (hd : star d = d) (he : star e = e) (i : Fin 15) :
    ∑ k : Fin 15, periodValue a b c d e i k * star (periodValue a b c d e i k) /
      (centralizerOrder k : ℂ) = (1 : ℂ) := by
  change (starRingEnd ℂ) a = a at ha
  change (starRingEnd ℂ) b = b at hb
  change (starRingEnd ℂ) c = c at hc
  change (starRingEnd ℂ) d = d at hd
  change (starRingEnd ℂ) e = e at he
  fin_cases i <;>
    norm_num [periodValue, Fin.sum_univ_succ, centralizerOrder, map_ofNat, star_add, star_mul, star_neg, ha, hb, hc, hd, he]
  all_goals first
    | linear_combination h5sq / 5
    | linear_combination hsq / 19

private theorem periodValue_injective (a b c d e : ℂ)
    (hab : a + b = -1) (habmul : a * b = -1)
    (hcde : c + d + e = -1) (hsq : c ^ 2 + d ^ 2 + e ^ 2 = 13) :
    Function.Injective (periodValue a b c d e) := by
  have habne : a ≠ b := by
    intro h
    have ha : 2 * a = -1 := by linear_combination hab + h
    have hfalse : (5 : ℂ) = 0 := by
      linear_combination 4 * habmul - (2 * a - 1) * ha + 4 * a * h
    norm_num at hfalse
  have hcd : ¬ (c = d ∧ d = e) := by
    rintro ⟨h, h'⟩
    have hc : 3 * c = -1 := by linear_combination hcde + 2 * h + h'
    have hfalse : (38 : ℂ) = 0 := by
      linear_combination (3 * c - 1) * hc - 3 * hsq -
        3 * (c + d) * h - 3 * (c + e) * (h + h')
    norm_num at hfalse
  intro i j hij
  have h0 := congrFun hij 0
  have h1 := congrFun hij 1
  have h3 := congrFun hij 3
  have h12 := congrFun hij 12
  have h13 := congrFun hij 13
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [periodValue] at h0
  all_goals norm_num [periodValue] at h1
  all_goals first
    | (change -2 * a = -2 * b at h3; exact (habne (by linear_combination -h3 / 2)).elim)
    | (change -2 * b = -2 * a at h3; exact (habne (by linear_combination h3 / 2)).elim)
    | (change a = b at h3; exact (habne h3).elim)
    | (change b = a at h3; exact (habne h3.symm).elim)
    | (change -a = -b at h3; exact (habne (neg_injective h3)).elim)
    | (change -b = -a at h3; exact (habne (neg_injective h3).symm).elim)
    | (change c = e at h12; change d = c at h13
       exact (hcd ⟨h13.symm, h13.trans h12⟩).elim)
    | (change c = d at h12; change d = e at h13
       exact (hcd ⟨h12, h13⟩).elim)
    | (change e = c at h12; change c = d at h13
       exact (hcd ⟨h13, h13.symm.trans h12.symm⟩).elim)
    | (change e = d at h12; change c = e at h13
       exact (hcd ⟨h13.trans h12, h12.symm⟩).elim)
    | (change d = c at h12; change e = d at h13
       exact (hcd ⟨h12.symm, h13.symm⟩).elim)
    | (change d = e at h12; change e = c at h13
       exact (hcd ⟨h13.symm.trans h12.symm, h12⟩).elim)

/-- The literal cyclotomic rows have norm one with the centralizer weights. -/
public theorem ordinaryValue_norm {ζ₅ ζ₁₉ : ℂ}
    (h₅ : IsPrimitiveRoot ζ₅ 5) (h₁₉ : IsPrimitiveRoot ζ₁₉ 19) (i : Fin 15) :
    ∑ j : Fin 15, ordinaryValue ζ₅ ζ₁₉ i j * star (ordinaryValue ζ₅ ζ₁₉ i j) /
      (centralizerOrder j : ℂ) = 1 := by
  obtain ⟨_, _, hs₅, ha, hb⟩ := five_periods h₅
  obtain ⟨_, hs₁₉, _, hc, hd, he⟩ := nineteen_periods h₁₉
  exact periodValue_norm _ _ _ _ _ hs₅ hs₁₉ ha hb hc hd he i

/-- Distinct rows remain distinct for every permitted choice of primitive roots. -/
public theorem ordinaryValue_injective {ζ₅ ζ₁₉ : ℂ}
    (h₅ : IsPrimitiveRoot ζ₅ 5) (h₁₉ : IsPrimitiveRoot ζ₁₉ 19) :
    Function.Injective (ordinaryValue ζ₅ ζ₁₉) := by
  obtain ⟨hs₅, hm₅, _, _, _⟩ := five_periods h₅
  obtain ⟨hs₁₉, hq₁₉, _, _, _, _⟩ := nineteen_periods h₁₉
  exact periodValue_injective _ _ _ _ _ hs₅ hm₅ hs₁₉ hq₁₉

/-- The identity column contains the indicated positive ordinary degrees. -/
public theorem ordinaryValue_identity (ζ₅ ζ₁₉ : ℂ) (i : Fin 15) :
    ordinaryValue ζ₅ ζ₁₉ i 0 = (ordinaryDegree i : ℂ) := by
  fin_cases i <;> simp [ordinaryValue, ordinaryDegree]

public theorem ordinaryDegree_pos (i : Fin 15) : 0 < ordinaryDegree i := by
  fin_cases i <;> decide

/-- The degree-square sum is the supplied group order. -/
public theorem ordinaryDegree_normSq_sum :
    ∑ i : Fin 15, Complex.normSq (ordinaryDegree i : ℂ) = (175560 : ℝ) := by
  norm_num [ordinaryDegree, Fin.sum_univ_succ, Complex.normSq_apply]

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
