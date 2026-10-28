module

public import Stellmacher.Recognition.LyonsU3Four.TableIConsecutiveResidualData

/-!
# Extracting the residual orbit counts in Case 5

The four distinguished Z₄ rows leave only periodic rows. Completing squares
bounds their entries, and a finite calculation exhausts the 33-row catalogue.
Galois symmetry identifies the counts in each orbit; subtracting the frame
from equation (3.2) gives the residual Gram equations, retaining all repeated
rows. The principal row ensures positivity of orbit count 6.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 379,
Case 5(a)–(c).
-/

@[expose] public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
namespace ConsecutiveResidual

private def q (t a b c : ℤ) : ℤ :=
  4*t^2+a^2+2*b^2+2*c^2+3*(2*(a-b)^2+2*(a-c)^2+4*(b-c)^2)
private theorem q_bounds (t a b c : ℤ) (h : q t a b c < 64) :
    (-3 ≤ t ∧ t ≤ 3) ∧ (-3 ≤ a ∧ a ≤ 3) ∧
    (-3 ≤ b ∧ b ≤ 3) ∧ (-3 ≤ c ∧ c ≤ 3) := by
  dsimp [q] at h
  have ht : 4*t^2 < 64 := by
    nlinarith only [h, sq_nonneg a, sq_nonneg b, sq_nonneg c,
      sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
  have ha : 4*a^2 < 64 := by
    nlinarith only [h, sq_nonneg t, sq_nonneg (3*a-2*b-2*c), sq_nonneg (b-c)]
  have hb : 4*b^2 < 64 := by
    nlinarith only [h, sq_nonneg t, sq_nonneg (10*c-3*a-6*b),
      sq_nonneg (7*a-6*b), sq_nonneg b]
  have hc : 4*c^2 < 64 := by
    nlinarith only [h, sq_nonneg t, sq_nonneg (10*b-3*a-6*c),
      sq_nonneg (7*a-6*c), sq_nonneg c]
  exact ⟨⟨by nlinarith only [ht], by nlinarith only [ht]⟩,
    ⟨by nlinarith only [ha], by nlinarith only [ha]⟩,
    ⟨by nlinarith only [hb], by nlinarith only [hb]⟩,
    ⟨by nlinarith only [hc], by nlinarith only [hc]⟩⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem finite_coverage : ∀ t a b c : Fin 7,
    q ((t:ℤ)-3) ((a:ℤ)-3) ((b:ℤ)-3) ((c:ℤ)-3) < 64 →
    Int.ModEq 4 ((t:ℤ)-3) (((a:ℤ)-3)+2*((b:ℤ)-3)+2*((c:ℤ)-3)) →
    0 < ((a:ℤ)-3)+2*((b:ℤ)-3)+2*((c:ℤ)-3) →
    -1 ≤ ((b:ℤ)-3)-((c:ℤ)-3) → ((b:ℤ)-3)-((c:ℤ)-3) ≤ 1 →
    ∃ k, ![((t:ℤ)-3), ((a:ℤ)-3), ((b:ℤ)-3), ((c:ℤ)-3),
      ((b:ℤ)-3), ((c:ℤ)-3)] = rows k := by decide
private theorem bounded_seven (x : ℤ) (h : -3 ≤ x ∧ x ≤ 3) :
    ∃ k : Fin 7, x = (k : ℤ) - 3 := by
  refine ⟨⟨(x+3).toNat, by omega⟩, ?_⟩
  change x = ((x+3).toNat : ℤ) - 3
  omega
private theorem periodic_covered (t a b c : ℤ) (hc : q t a b c < 64)
    (hm : Int.ModEq 4 t (a+2*b+2*c)) (hp : 0 < a+2*b+2*c)
    (hb : -1 ≤ b-c ∧ b-c ≤ 1) : ∃ k, ![t,a,b,c,b,c] = rows k := by
  obtain ⟨ht,ha,hb',hc'⟩ := q_bounds t a b c hc
  obtain ⟨t',rfl⟩ := bounded_seven t ht
  obtain ⟨a',rfl⟩ := bounded_seven a ha
  obtain ⟨b',rfl⟩ := bounded_seven b hb'
  obtain ⟨c',rfl⟩ := bounded_seven c hc'
  exact finite_coverage t' a' b' c' hc hm hp hb.1 hb.2
private theorem q_sign (s t a b c : ℤ) (hs : s^2 = 1) :
    q (s*t) (s*a) (s*b) (s*c) = q t a b c := by
  simp only [q, ← mul_sub, mul_pow, hs, one_mul]

private def rotate (r : TableIRow) : TableIRow := ![r 0,r 1,r 3,r 4,r 5,r 2]
private theorem rotate_injective : Function.Injective rotate := by
  intro r s h
  funext k
  fin_cases k
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 5
  · exact congrFun h 2
  · exact congrFun h 3
  · exact congrFun h 4
private def representative : Fin 23 → Fin 33 :=
  ![0,2,3,5,7,8,9,10,12,14,15,16,18,19,21,22,23,25,26,27,29,30,32]
private theorem rows_representative (k : Fin 33) :
    rows k = rows (representative (orbit k)) ∨
    rows k = rotate (rows (representative (orbit k))) := by
  revert k; decide
private def support : Fin 4 ⊕ Fin 33 → TableIRow :=
  Sum.elim (fun k => TableICatalogue.z4 k.succ) rows
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem support_injective : Function.Injective support := by decide
end ConsecutiveResidual
open ConsecutiveResidual
variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

/-- Every normalized periodic row belongs to the residual catalogue. -/
theorem normalized_periodic_mem_residual (principal : I)
    (h : d.TableIPatternHypotheses principal) (hl : ¬ d.HasLargeDifference)
    (j : I) (hp : d.iDz 1 j = d.iDz 3 j ∧ d.iDz 2 j = d.iDz 4 j) :
    ∃ k, d.normalizedTableIRow j = ConsecutiveResidual.rows k := by
  let s := d.tableIRowSign j
  have hz : d.zValue j = d.iDz 0 j + 2*d.iDz 1 j + 2*d.iDz 2 j := by
    simp [zValue, Fin.sum_univ_succ, ← hp.1, ← hp.2]
    ring
  have hq : q (d.dT j) (d.iDz 0 j) (d.iDz 1 j) (d.iDz 2 j) =
      d.contribution j := by
    have hi (i : Fin 5) : Finset.Iio i = Finset.univ.filter (· < i) := by
      ext k; simp
    simp [contribution, hi, Finset.sum_filter, Fin.sum_univ_succ, q, ← hp.1, ← hp.2]
    ring
  have hc : q (s*d.dT j) (s*d.iDz 0 j) (s*d.iDz 1 j) (s*d.iDz 2 j) < 64 := by
    rw [ConsecutiveResidual.q_sign _ _ _ _ _ (d.tableIRowSign_sq j), hq]
    exact h.equation_3_3 j
  have hm : Int.ModEq 4 (s*d.dT j) (s*d.iDz 0 j + 2*(s*d.iDz 1 j)+2*(s*d.iDz 2 j)) := by
    convert (h.equation_3_4 j).mul_left s using 1
    rw [hz]; ring
  have hspos : 0 < s*d.zValue j := by
    have hn := h.z_nonzero j
    dsimp [s, tableIRowSign]
    split_ifs <;> omega
  have hpos : 0 < s*d.iDz 0 j + 2*(s*d.iDz 1 j)+2*(s*d.iDz 2 j) := by
    rw [hz] at hspos
    nlinarith only [hspos]
  have hb : -1 ≤ s*d.iDz 1 j - s*d.iDz 2 j ∧
      s*d.iDz 1 j - s*d.iDz 2 j ≤ 1 := by
    have hb := h.equation_3_2.unit_bounds_of_not_large d hl 0 j
    change -1 ≤ d.iDz 1 j - d.iDz 2 j ∧ d.iDz 1 j - d.iDz 2 j ≤ 1 at hb
    dsimp [s, tableIRowSign]
    split_ifs <;> simp only [one_mul, neg_one_mul] <;> omega
  obtain ⟨k,hk⟩ := ConsecutiveResidual.periodic_covered _ _ _ _ hc hm hpos hb
  refine ⟨k, ?_⟩
  rw [← hk]
  funext i
  fin_cases i <;> simp [normalizedTableIRow, tableIRow, s, ← hp.1, ← hp.2]
omit [Fintype I] in
private theorem normalized_rotation (hg : d.GaloisSymmetry) :
    ∃ σ : Equiv.Perm I, ∀ j,
      d.normalizedTableIRow (σ j) = rotate (d.normalizedTableIRow j) := by
  obtain ⟨σ,hσ⟩ := hg
  have ht (j : I) : d.dT (σ j) = d.dT j := (hσ j).1.symm
  have hz (j : I) (i : Fin 5) : d.iDz i (σ j) = d.iDz (![0,2,3,4,1] i) j := by
    fin_cases i
    · exact ((hσ j).2 0).symm
    · exact ((hσ j).2 2).symm
    · exact ((hσ j).2 3).symm
    · exact ((hσ j).2 4).symm
    · exact ((hσ j).2 1).symm
  have hv (j : I) : d.zValue (σ j) = d.zValue j := by
    simp [zValue, hz, Fin.sum_univ_succ]
    ring
  have hs (j : I) : d.tableIRowSign (σ j) = d.tableIRowSign j := by
    simp only [tableIRowSign, hv]
  refine ⟨σ, ?_⟩
  intro j
  funext k
  fin_cases k <;> simp [normalizedTableIRow, tableIRow, rotate, ht, hz, hs]
private theorem multiplicity_rotation (hg : d.GaloisSymmetry) (r : TableIRow) :
    d.tableIRowMultiplicity (rotate r) = d.tableIRowMultiplicity r := by
  classical
  obtain ⟨σ,hσ⟩ := d.normalized_rotation hg
  symm
  apply Fintype.card_congr (σ.subtypeEquiv _)
  intro j
  rw [hσ, rotate_injective.eq_iff]
private theorem orbit_multiplicity (hg : d.GaloisSymmetry) (k : Fin 33) :
    d.tableIRowMultiplicity (rows k) =
      d.tableIRowMultiplicity (rows (representative (orbit k))) := by
  rcases rows_representative k with hk | hk
  · rw [hk]
  · rw [hk, d.multiplicity_rotation hg]
private theorem support_coverage (principal : I)
    (h : d.TableIPatternHypotheses principal) (hl : ¬ d.HasLargeDifference)
    (f : Fin 4 ↪ I) (hf : ∀ k, d.normalizedTableIRow (f k) = TableICatalogue.z4 k.succ)
    (hr : ∀ j, j ∉ Set.range f → d.iDz 1 j = d.iDz 3 j ∧ d.iDz 2 j = d.iDz 4 j)
    (j : I) : ∃ k, d.normalizedTableIRow j = support k := by
  by_cases hj : j ∈ Set.range f
  · obtain ⟨k,rfl⟩ := hj
    exact ⟨Sum.inl k, hf k⟩
  · obtain ⟨k,hk⟩ := d.normalized_periodic_mem_residual principal h hl j (hr j hj)
    exact ⟨Sum.inr k,hk⟩
private theorem frame_fiber (principal : I)
    (h : d.TableIPatternHypotheses principal) (hl : ¬ d.HasLargeDifference)
    (f : Fin 4 ↪ I) (hf : ∀ k, d.normalizedTableIRow (f k) = TableICatalogue.z4 k.succ)
    (hr : ∀ j, j ∉ Set.range f → d.iDz 1 j = d.iDz 3 j ∧ d.iDz 2 j = d.iDz 4 j)
    (k : Fin 4) (j : I) : d.normalizedTableIRow j = TableICatalogue.z4 k.succ ↔ j = f k := by
  constructor
  · intro hj
    by_cases hjf : j ∈ Set.range f
    · obtain ⟨l,rfl⟩ := hjf
      have he : support (Sum.inl l) = support (Sum.inl k) := (hf l).symm.trans hj
      have hk := support_injective he
      exact congrArg f (Sum.inl.inj hk)
    · obtain ⟨l,hl⟩ := d.normalized_periodic_mem_residual principal h hl j (hr j hjf)
      have he : support (Sum.inr l) = support (Sum.inl k) := hl.symm.trans hj
      cases support_injective he
  · rintro rfl; exact hf k
private theorem frame_multiplicity (principal : I)
    (h : d.TableIPatternHypotheses principal) (hl : ¬ d.HasLargeDifference)
    (f : Fin 4 ↪ I) (hf : ∀ k, d.normalizedTableIRow (f k) = TableICatalogue.z4 k.succ)
    (hr : ∀ j, j ∉ Set.range f → d.iDz 1 j = d.iDz 3 j ∧ d.iDz 2 j = d.iDz 4 j)
    (k : Fin 4) : d.tableIRowMultiplicity (TableICatalogue.z4 k.succ) = 1 := by
  classical
  unfold tableIRowMultiplicity
  calc
    _ = Fintype.card {j // j = f k} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (d.frame_fiber principal h hl f hf hr k))
    _ = 1 := Fintype.card_subtype_eq (f k)
private theorem sum_support {R : Type*} [Semiring R]
    (hc : ∀ j, ∃ k, d.normalizedTableIRow j = support k) (F : TableIRow → R) :
    ∑ k, (d.tableIRowMultiplicity (support k) : R) * F (support k) =
      ∑ j, F (d.normalizedTableIRow j) := by
  classical
  have hm (r : TableIRow) : (d.tableIRowMultiplicity r : R) =
      ∑ j, if d.normalizedTableIRow j = r then (1:R) else 0 := by
    simp [tableIRowMultiplicity, Fintype.card_subtype, Finset.sum_boole]
  simp_rw [hm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨k,hk⟩ := hc j
  rw [hk]
  simp [support_injective.eq_iff]
private theorem multiplicity_support
    (hc : ∀ j, ∃ k, d.normalizedTableIRow j = support k) (r : TableIRow) :
    d.tableIRowMultiplicity r =
      ∑ k, if support k = r then d.tableIRowMultiplicity (support k) else 0 := by
  classical
  have he := d.sum_support hc (fun s => if s = r then (1:ℕ) else 0)
  simp only [mul_ite, mul_one, mul_zero, Nat.cast_id] at he
  rw [he]
  simp [tableIRowMultiplicity, Fintype.card_subtype, Finset.sum_boole]
private def fullGram (i j : Fin 6) : ℤ :=
  if i = 0 then (if j = 0 then 16 else 0)
  else if j = 0 then 0 else 4 * (3 + if i = j then 1 else 0)
private theorem normalized_gram (he : d.Equation3_2) (i j : Fin 6) :
    ∑ k, d.normalizedTableIRow k i * d.normalizedTableIRow k j = fullGram i j := by
  have hs (k : I) : d.normalizedTableIRow k i * d.normalizedTableIRow k j =
      d.tableIRow k i * d.tableIRow k j := by
    dsimp [normalizedTableIRow]
    calc
      _ = d.tableIRowSign k ^ 2 * (d.tableIRow k i * d.tableIRow k j) := by ring
      _ = _ := by rw [d.tableIRowSign_sq, one_mul]
  simp_rw [hs]
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact he.tt
    · simpa [fullGram, tableIRow_zero, tableIRow_succ, columnInner] using he.tz j
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa [fullGram, tableIRow_zero, tableIRow_succ, columnInner, mul_comm] using he.tz i
    · simpa [fullGram, tableIRow_succ, columnInner] using he.zz i j
private theorem gram_subtract_frame (i j : Fin 6) :
    fullGram i j - (∑ k : Fin 4, TableICatalogue.z4 k.succ i * TableICatalogue.z4 k.succ j) =
      gramTarget i j := by
  revert i j; decide
/-- Extract all 23 residual Galois-orbit counts after the forced Z₄ frame,
including the Gram equations and the full normalized row multiplicities. -/
theorem exists_consecutiveResidual_counts (principal : I)
    (h : d.TableIPatternHypotheses principal) (hl : ¬ d.HasLargeDifference)
    (hf : d.HasZ4Frame) :
    ∃ n : Fin 23 → ℕ, CountConstraints n ∧
      ∀ r, d.tableIRowMultiplicity r = ConsecutiveResidual.multiplicity n r := by
  classical
  obtain ⟨f,hf,hr⟩ := hf
  let n : Fin 23 → ℕ := fun k => d.tableIRowMultiplicity (rows (representative k))
  have hn (k : Fin 33) : d.tableIRowMultiplicity (rows k) = n (orbit k) :=
    d.orbit_multiplicity h.galois_symmetry k
  have hc := d.support_coverage principal h hl f hf hr
  have hm := d.frame_multiplicity principal h hl f hf hr
  refine ⟨n, ⟨?_, ?_⟩, ?_⟩
  · intro i j
    have he := d.sum_support hc (fun r => r i * r j)
    rw [Fintype.sum_sum_type] at he
    simp only [support, Sum.elim_inl, Sum.elim_inr, hm, Nat.cast_one, one_mul, hn] at he
    have hres : (∑ k : Fin 33, (n (orbit k):ℤ) * (rows k i * rows k j)) = gram n i j := by
      simp only [gram, mul_assoc]
    rw [hres, d.normalized_gram h.equation_3_2] at he
    rw [← gram_subtract_frame]
    omega
  · change 0 < Fintype.card {j // d.normalizedTableIRow j = rows 9}
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨principal, d.normalizedTableIRow_principal principal h⟩⟩
  · intro r
    rw [d.multiplicity_support hc, Fintype.sum_sum_type]
    simp only [support, Sum.elim_inl, Sum.elim_inr, hm, hn, ConsecutiveResidual.multiplicity]

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
