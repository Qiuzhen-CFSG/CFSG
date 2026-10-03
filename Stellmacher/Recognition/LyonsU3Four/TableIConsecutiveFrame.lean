module
public import Stellmacher.Recognition.LyonsU3Four.TableIDifferenceColumns
public import Stellmacher.Recognition.LyonsU3Four.TableIRowMultiplicity
public import Stellmacher.Recognition.LyonsU3Four.TableIColumnReflection

/-!
# The forced Z₄ frame in Lyons's Case 5

A consecutive pair of equal unit differences forces four distinct rotating
rows. The nonnegative products `(₁dᶻ − ₂dᶻ)(₁dᶻ − ₃dᶻ)` sum to four;
the principal row contributes one. This forces the central entry of the
rotating rows to equal their middle entry. The strict contribution bound and
congruence then determine the common sign and the order-four entry, giving
exactly the four nonprincipal rows of Z₄ after normalization.

The opposite-column differences on these four rows exhaust their squared
norms. Thus every remaining row has period two. This is the initial reduction
of Case 5, not the residual enumeration into H, J, K, L.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 379,
Case 5, before alternatives (a)–(c).
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
open scoped BigOperators
variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

theorem consecutive_unit_shape (he : d.Equation3_2)
    (hl : ¬ d.HasLargeDifference) (j : I)
    (hj : d.adjacentDifference 0 j * d.adjacentDifference 1 j = 1) :
    ∃ s : ℤ, s ^ 2 = 1 ∧
      (fun i => d.adjacentDifference i j) = ![s, s, -s, -s] := by
  have h0 := he.unit_bounds_of_not_large d hl 0 j
  have h1 := he.unit_bounds_of_not_large d hl 1 j
  have h2 := he.unit_bounds_of_not_large d hl 2 j
  have h3 := he.unit_bounds_of_not_large d hl 3 j
  have hz : d.adjacentDifference 0 j + (d.adjacentDifference 1 j +
      (d.adjacentDifference 2 j + d.adjacentDifference 3 j)) = 0 := by
    simpa [Fin.sum_univ_succ] using d.adjacentDifference_sum j
  have hs : d.adjacentDifference 0 j = 1 ∨ d.adjacentDifference 0 j = -1 := by
    have hne : d.adjacentDifference 0 j ≠ 0 := by
      intro h
      rw [h] at hj
      norm_num at hj
    omega
  refine ⟨d.adjacentDifference 0 j, ?_, ?_⟩
  · rcases hs with hs | hs <;> rw [hs] <;> norm_num
  · funext i
    rcases hs with hs | hs
    · rw [hs] at hj
      norm_num at hj
      fin_cases i <;> dsimp <;> omega
    · rw [hs] at hj
      norm_num at hj
      fin_cases i <;> dsimp <;> omega

/-- A rotating consecutive-difference orbit, before the common row sign is fixed. -/
def consecutiveRowMatrix (t a b s : ℤ) : Fin 4 → TableIRow :=
  ![![t, a, b+s, b, b-s, b], ![t, a, b, b-s, b, b+s],
    ![t, a, b-s, b, b+s, b], ![t, a, b, b+s, b, b-s]]

private theorem consecutiveRowMatrix_injective (t a b s : ℤ) (hs : s ≠ 0) :
    Function.Injective (consecutiveRowMatrix t a b s) := by
  intro i j hij
  have h2 := congrFun hij (2 : Fin 6)
  have h3 := congrFun hij (3 : Fin 6)
  fin_cases i <;> fin_cases j <;>
    norm_num [consecutiveRowMatrix] at h2 h3 ⊢ <;>
    simp only [Matrix.cons_val] at h2 h3 <;> omega

theorem consecutive_row_frame (he : d.Equation3_2)
    (hg : d.GaloisSymmetry) (hl : ¬ d.HasLargeDifference)
    (hc : d.HasConsecutiveUnitDifferences) :
    ∃ (t a b s : ℤ) (f : Fin 4 ↪ I), s ^ 2 = 1 ∧
      ∀ k, d.tableIRow (f k) = consecutiveRowMatrix t a b s k := by
  obtain ⟨j, hj⟩ := hc
  obtain ⟨s, hs, hj⟩ := d.consecutive_unit_shape he hl j hj
  obtain ⟨σ, hσ⟩ := hg
  let f : Fin 4 → I := ![j, σ j, σ (σ j), σ (σ (σ j))]
  have ht (k : I) : d.dT (σ k) = d.dT k := (hσ k).1.symm
  have rot (k : I) (i : Fin 5) : d.iDz i (σ k) =
      d.iDz (![0, 2, 3, 4, 1] i) k := by
    fin_cases i
    · exact ((hσ k).2 0).symm
    · exact ((hσ k).2 2).symm
    · exact ((hσ k).2 3).symm
    · exact ((hσ k).2 4).symm
    · exact ((hσ k).2 1).symm
  have h0 := congrFun hj 0
  have h1 := congrFun hj 1
  have h2 := congrFun hj 2
  have h3 := congrFun hj 3
  simp [adjacentDifference] at h0 h1 h2 h3
  have hf (k : Fin 4) : d.tableIRow (f k) =
      consecutiveRowMatrix (d.dT j) (d.iDz 0 j) (d.iDz 2 j) s k := by
    funext i
    fin_cases k <;> fin_cases i <;>
      simp [f, tableIRow, consecutiveRowMatrix, ht, rot] <;> omega
  have hi : Function.Injective f := by
    intro a b hab
    have hn : s ≠ 0 := by
      intro hz
      rw [hz] at hs
      norm_num at hs
    apply consecutiveRowMatrix_injective _ _ _ s hn
    exact (hf a).symm.trans ((congrArg d.tableIRow hab).trans (hf b))
  exact ⟨d.dT j, d.iDz 0 j, d.iDz 2 j, s, ⟨f, hi⟩, hs, hf⟩

private theorem adjacent_product_nonneg (he : d.Equation3_2)
    (hl : ¬ d.HasLargeDifference) (j : I) :
    0 ≤ (d.iDz 0 j - d.iDz 1 j) * (d.iDz 0 j - d.iDz 2 j) := by
  have hb := he.unit_bounds_of_not_large d hl 0 j
  change -1 ≤ d.iDz 1 j - d.iDz 2 j ∧ d.iDz 1 j - d.iDz 2 j ≤ 1 at hb
  have hc : (d.iDz 0 j - d.iDz 1 j ≤ 0 ∧ d.iDz 0 j - d.iDz 2 j ≤ 0) ∨
      (0 ≤ d.iDz 0 j - d.iDz 1 j ∧ 0 ≤ d.iDz 0 j - d.iDz 2 j) := by omega
  rcases hc with hc | hc
  · exact mul_nonneg_of_nonpos_of_nonpos hc.1 hc.2
  · exact mul_nonneg hc.1 hc.2

/-- The principal row leaves too little positive inner product for a shift of
    the central involution entry in the rotating orbit. -/
theorem consecutive_row_frame_center (principal : I)
    (h : d.TableIPatternHypotheses principal) (hl : ¬ d.HasLargeDifference)
    (t a b s : ℤ) (f : Fin 4 ↪ I) (hs : s ^ 2 = 1)
    (hf : ∀ k, d.tableIRow (f k) = consecutiveRowMatrix t a b s k) : a = b := by
  classical
  let q (j : I) : ℤ := (d.iDz 0 j - d.iDz 1 j) * (d.iDz 0 j - d.iDz 2 j)
  have hq (j : I) : 0 ≤ q j := d.adjacent_product_nonneg h.equation_3_2 hl j
  have total : ∑ j, q j = 4 := by
    have he := h.equation_3_2.difference_inner d 0 1 0 2
    norm_num [columnInner] at he
    exact he
  have qp : q principal = 1 := by simp [q, h.principal_iDz]
  have vals (k : Fin 4) : q (f k) =
      (consecutiveRowMatrix t a b s k 1 - consecutiveRowMatrix t a b s k 2) *
      (consecutiveRowMatrix t a b s k 1 - consecutiveRowMatrix t a b s k 3) := by
    have h1 := congrFun (hf k) 1
    have h2 := congrFun (hf k) 2
    have h3 := congrFun (hf k) 3
    change d.iDz 0 (f k) = _ at h1
    change d.iDz 1 (f k) = _ at h2
    change d.iDz 2 (f k) = _ at h3
    simp only [q, h1, h2, h3]
  have sumframe : ∑ k, q (f k) = 4 * (a-b)^2 := by
    simp only [vals, Fin.sum_univ_succ]
    simp [consecutiveRowMatrix]
    ring
  have hp : principal ∉ Finset.univ.image f := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro k hk
    have h2 := congrFun (hf k) 2
    have h3 := congrFun (hf k) 3
    rw [hk, d.tableIRow_principal principal h] at h2 h3
    fin_cases k <;> norm_num [consecutiveRowMatrix] at h2 h3 <;>
      simp only [Matrix.cons_val] at h2 h3 <;> nlinarith
  have hb : 1 + 4 * (a-b)^2 ≤ 4 := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (insert principal (Finset.univ.image f)))
      (fun j _ _ => hq j)
    rw [Finset.sum_insert hp, Finset.sum_image f.injective.injOn, qp, sumframe, total] at hh
    exact hh
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-b-1), sq_nonneg (a-b+1)]

/-- The contribution and congruence fix the common sign and the order-four entry. -/
theorem consecutive_row_frame_scalar (principal : I)
    (h : d.TableIPatternHypotheses principal)
    (t a s : ℤ) (f : Fin 4 ↪ I) (hs : s ^ 2 = 1)
    (hf : ∀ k, d.tableIRow (f k) = consecutiveRowMatrix t a a s k) :
    a ^ 2 = 1 ∧ t = a := by
  have ht : d.dT (f 0) = t := congrFun (hf 0) 0
  have hz (i : Fin 5) : d.iDz i (f 0) = ![a, a+s, a, a-s, a] i := by
    have hh := congrFun (hf 0) i.succ
    fin_cases i <;> exact hh
  have hv : d.zValue (f 0) = 5 * a := by
    simp [zValue, hz, Fin.sum_univ_succ]
    ring
  have ha : a ≠ 0 := by
    intro ha
    exact h.z_nonzero (f 0) (by rw [hv, ha]; ring)
  have hc : 4 * t ^ 2 + 5 * a ^ 2 + 32 < 64 := by
    have hb := h.equation_3_3 (f 0)
    have hIio (i : Fin 5) : Finset.Iio i = Finset.univ.filter (fun k => k < i) := by
      ext k
      simp
    have hh : d.contribution (f 0) = 4 * t ^ 2 + 5 * a ^ 2 + 32 := by
      simp only [contribution, hIio, Finset.sum_filter, ht, hz, Fin.sum_univ_succ]
      norm_num [Fin.lt_def, Matrix.cons_val, Fin.reduceFinMk]
      simp only [Matrix.cons_val]
      nlinarith [hs]
    rwa [hh] at hb
  have hm := h.equation_3_4 (f 0)
  rw [ht, hv] at hm
  have haB : -2 ≤ a ∧ a ≤ 2 := by constructor <;> nlinarith [sq_nonneg t]
  have htB := h.equation_3_3.dT_bounds d (f 0)
  rw [ht] at htB
  change t % 4 = (5 * a) % 4 at hm
  obtain ⟨haL, haU⟩ := haB
  obtain ⟨htL, htU⟩ := htB
  interval_cases a <;> interval_cases t <;> norm_num at *

private theorem zero_off_frame {J : Type*} [Fintype J]
    (v : I → ℤ) (f : J ↪ I)
    (he : ∑ j, v j ^ 2 = ∑ k, v (f k) ^ 2) (j : I)
    (hj : j ∉ Set.range f) : v j = 0 := by
  classical
  let S := Finset.univ.image f
  have him : ∑ k ∈ S, v k ^ 2 = ∑ k, v (f k) ^ 2 :=
    Finset.sum_image f.injective.injOn
  have hh := Finset.sum_sdiff (f := fun k => v k ^ 2) (Finset.subset_univ S)
  rw [him, he] at hh
  have hz : ∑ k ∈ Finset.univ \ S, v k ^ 2 = 0 := by omega
  have hjS : j ∈ Finset.univ \ S := by simpa [S] using hj
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k (_ : k ∈ Finset.univ \ S) => sq_nonneg (v k))).mp hz j hjS
  exact sq_eq_zero_iff.mp hsq

/-- All rows outside the four rotating rows have period two. -/
theorem consecutive_row_frame_remaining (he : d.Equation3_2)
    (t a b s : ℤ) (f : Fin 4 ↪ I) (hs : s ^ 2 = 1)
    (hf : ∀ k, d.tableIRow (f k) = consecutiveRowMatrix t a b s k)
    (j : I) (hj : j ∉ Set.range f) :
    d.iDz 1 j = d.iDz 3 j ∧ d.iDz 2 j = d.iDz 4 j := by
  have vals (k : Fin 4) (i : Fin 5) :
      d.iDz i (f k) = consecutiveRowMatrix t a b s k i.succ := by
    simpa only [tableIRow_succ] using congrFun (hf k) i.succ
  have norm13 : ∑ j, (d.iDz 1 j - d.iDz 3 j) ^ 2 = 8 := by
    have hh := he.difference_inner d 1 3 1 3
    norm_num [columnInner, ← pow_two] at hh
    exact hh
  have norm24 : ∑ j, (d.iDz 2 j - d.iDz 4 j) ^ 2 = 8 := by
    have hh := he.difference_inner d 2 4 2 4
    norm_num [columnInner, ← pow_two] at hh
    exact hh
  have frame13 : ∑ k, (d.iDz 1 (f k) - d.iDz 3 (f k)) ^ 2 = 8 := by
    simp only [vals, Fin.sum_univ_succ]
    simp [consecutiveRowMatrix]
    nlinarith [hs]
  have frame24 : ∑ k, (d.iDz 2 (f k) - d.iDz 4 (f k)) ^ 2 = 8 := by
    simp only [vals, Fin.sum_univ_succ]
    simp [consecutiveRowMatrix]
    nlinarith [hs]
  constructor
  · exact sub_eq_zero.mp (zero_off_frame (fun k => d.iDz 1 k - d.iDz 3 k) f
      (norm13.trans frame13.symm) j hj)
  · exact sub_eq_zero.mp (zero_off_frame (fun k => d.iDz 2 k - d.iDz 4 k) f
      (norm24.trans frame24.symm) j hj)

/-- The four nonprincipal rows of Z₄ occur once as distinguished rows;
    every remaining row has period two in its last four entries. -/
def HasZ4Frame : Prop :=
  ∃ f : Fin 4 ↪ I,
    (∀ k, d.normalizedTableIRow (f k) = TableICatalogue.z4 k.succ) ∧
    ∀ j, j ∉ Set.range f → d.iDz 1 j = d.iDz 3 j ∧ d.iDz 2 j = d.iDz 4 j

private def consecutiveHalfTurn : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- The initial reduction of source Case 5, including the principal-row
    obstruction to shifted versions of the rotating orbit. -/
theorem hasZ4Frame_of_consecutive (principal : I)
    (h : d.TableIPatternHypotheses principal) (hl : ¬ d.HasLargeDifference)
    (hc : d.HasConsecutiveUnitDifferences) : d.HasZ4Frame := by
  obtain ⟨t, a, b, s, f, hs, hf⟩ :=
    d.consecutive_row_frame h.equation_3_2 h.galois_symmetry hl hc
  have hab := d.consecutive_row_frame_center principal h hl t a b s f hs hf
  subst b
  obtain ⟨ha, ht⟩ := d.consecutive_row_frame_scalar principal h t a s f hs hf
  subst t
  have hr := d.consecutive_row_frame_remaining h.equation_3_2 a a a s f hs hf
  have hv (k : Fin 4) : d.zValue (f k) = 5 * a := by
    simp only [zValue, ← tableIRow_succ, hf, Fin.sum_univ_succ]
    fin_cases k <;> simp [consecutiveRowMatrix, Matrix.cons_val] <;> ring
  have hn (k : Fin 4) : d.normalizedTableIRow (f k) =
      fun i => (if 0 < 5 * a then 1 else -1) * consecutiveRowMatrix a a a s k i := by
    funext i
    simp only [normalizedTableIRow, tableIRowSign, hv, hf]
  let g : Fin 4 ↪ I := consecutiveHalfTurn.toEmbedding.trans f
  have hg (k : Fin 4) : g k = f (consecutiveHalfTurn k) := rfl
  have gr (j : I) (hj : j ∉ Set.range g) :
      d.iDz 1 j = d.iDz 3 j ∧ d.iDz 2 j = d.iDz 4 j := by
    apply hr j
    rintro ⟨k, rfl⟩
    apply hj
    exact ⟨consecutiveHalfTurn.symm k, by simp [hg]⟩
  rcases sq_eq_one_iff.mp ha with ha | ha <;>
    rcases sq_eq_one_iff.mp hs with hs | hs
  · refine ⟨f, ?_, hr⟩
    intro k
    rw [hn]
    subst a; subst s
    funext i
    fin_cases k <;> fin_cases i <;> rfl
  · refine ⟨g, ?_, gr⟩
    intro k
    rw [hg, hn]
    subst a; subst s
    funext i
    fin_cases k <;> fin_cases i <;> rfl
  · refine ⟨g, ?_, gr⟩
    intro k
    rw [hg, hn]
    subst a; subst s
    funext i
    fin_cases k <;> fin_cases i <;> rfl
  · refine ⟨f, ?_, hr⟩
    intro k
    rw [hn]
    subst a; subst s
    funext i
    fin_cases k <;> fin_cases i <;> rfl

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
