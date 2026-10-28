module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.Arithmetic
public import Theory.Character.InnerProductByClasses

/-!
# Necessary numerical and character identities for a genuine real stem

The alternating sum of the eleven vertex characters vanishes on the regular
classes by line incidence. Ordinary orthogonality extracts its coefficient
at each row. The only omitted class is the order-eleven class; the trivial
first row fixes the normalization there. Consequently its table values
alternate along the stem. No sign constraint is assumed.

Successive subtraction also recovers the actual simple lifted characters
and natural dimensions. These results connect the exact finite ordering
calculation to `RealStem` and its literal tensor pairing, with no additional
subgroup data. Source: the ordinary J1 table and the real-stem incidence of
Feit, Chapter VII; see `../Source.md`.
-/

open scoped BigOperators
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

open PathOrdering

private theorem alternating_line (v : Fin 10 → ℂ) :
    ∑ i : Fin 11, (vertexSign i : ℂ) * lineIncidence v i = 0 := by
  simp [Fin.sum_univ_succ, vertexSign, lineIncidence]

private theorem value_nine (z w : ℂ) (i : Fin 15) :
    ordinaryValue z w i 9 = (ordinarySign i : ℂ) := by
  fin_cases i <;> simp [ordinaryValue, ordinarySign]

private theorem regular_iff (i : Fin 15) : ¬ 11 ∣ classOrder i ↔ i ≠ 9 := by
  fin_cases i <;> decide

/-- The ordinary signs at the eleven-singular class alternate along the actual stem. -/
public theorem RealStem.row_sign {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) (i : Fin 11) : ordinarySign (s.row i) = vertexSign i := by
  classical
  let ψ : ConjClassFunction G := ∑ j : Fin 11, (vertexSign j : ℂ) • d.chi (s.row j)
  have hcoeff (j : Fin 11) : classFunctionInner ψ (d.chi (s.row j)) =
      (vertexSign j : ℂ) := by
    dsimp only [ψ]
    rw [classFunctionInner_sum_left]
    simp [completeFamily_orthonormal d.complete, s.row_injective.eq_iff]
  have hvanish (c : Fin 15) (hc : c ≠ 9) : ψ (d.classes c) = 0 := by
    have hreg : ¬ 11 ∣ orderOf (d.representatives c) := by
      rw [d.orders]
      exact (regular_iff c).2 hc
    have hd (j : Fin 11) : d.chi (s.row j) (d.classes c) =
        lineIncidence (fun k => s.roots.value (s.rep k) (d.representatives c)) j := by
      rw [d.classes_eq]
      exact s.decomposition _ hreg j
    dsimp only [ψ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [hd]
    exact alternating_line _
  have hinner (j : Fin 11) : classFunctionInner ψ (d.chi (s.row j)) =
      ψ (d.classes 9) * (ordinarySign (s.row j) : ℂ) / 11 := by
    have hr : Function.Bijective (fun c => ConjClasses.mk (d.representatives c)) := by
      simpa only [← d.classes_eq] using d.classes.bijective
    rw [classFunctionInner_eq_sum_div_centralizer d.representatives hr]
    simp_rw [← d.classes_eq, d.centralizers]
    rw [Finset.sum_eq_single (9 : Fin 15)]
    · rw [d.values, value_nine]
      simp [centralizerOrder]
    · intro c _ hc
      rw [hvanish c hc]
      simp
    · simp
  have hzero : ψ (d.classes 9) / 11 = 1 := by
    have h := (hinner 0).symm.trans (hcoeff 0)
    simpa [s.first_row, ordinarySign, vertexSign] using h
  have hi : (vertexSign i : ℂ) = (ordinarySign (s.row i) : ℂ) := by
    calc
      (vertexSign i : ℂ) = ψ (d.classes 9) * (ordinarySign (s.row i) : ℂ) / 11 :=
        (hcoeff i).symm.trans (hinner i)
      _ = ψ (d.classes 9) / 11 * (ordinarySign (s.row i) : ℂ) := by ring
      _ = (ordinarySign (s.row i) : ℂ) := by rw [hzero, one_mul]
  exact_mod_cast hi.symm

/-- Exact integer dimensions of the edges computed by successive subtraction. -/
public theorem RealStem.edgeTerms_degree {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) :
    edgeTerms (fun i => (ordinaryDegree (s.row i) : ℤ)) = fun i => (s.degree i : ℤ) := by
  have hd : (fun i => (ordinaryDegree (s.row i) : ℤ)) =
      lineIncidence (fun i => (s.degree i : ℤ)) := by
    funext i
    rw [← s.degree_incidence]
    fin_cases i <;> simp [lineIncidence]
  rw [hd, edgeTerms_lineIncidence]

/-- Every actual stem satisfies all the finite candidate constraints. -/
public theorem RealStem.admissible {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) : Admissible s.row where
  injective := s.row_injective
  first := s.first_row
  nonzero_defect := s.row_nonzero_defect
  alternating := s.row_sign
  positive := by
    intro i
    rw [s.edgeTerms_degree]
    dsimp only
    exact_mod_cast s.degree_pos i
  last := by
    rw [s.edgeTerms_degree]
    dsimp only
    have h := s.degree_incidence 10
    change s.degree 9 = ordinaryDegree (s.row 10) at h
    exact_mod_cast h

/-- On every regular class, the edge recurrence equals the genuine lifted
simple character, not merely its reduction in characteristic eleven. -/
public theorem RealStem.value_eq_edgeTerms {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) (i : Fin 10) (c : Fin 15) (hc : c ≠ 9) :
    s.roots.value (s.rep i) (d.representatives c) =
      edgeTerms (fun j => ordinaryValue d.rootFive d.rootNineteen (s.row j) c) i := by
  have hreg : ¬ 11 ∣ orderOf (d.representatives c) := by
    rw [d.orders]
    exact (regular_iff c).2 hc
  have hd : (fun j => ordinaryValue d.rootFive d.rootNineteen (s.row j) c) =
      lineIncidence (fun j => s.roots.value (s.rep j) (d.representatives c)) := by
    funext j
    rw [← d.values, d.classes_eq]
    exact s.decomposition _ hreg j
  rw [hd, edgeTerms_lineIncidence]

/-- Application of the recurrence to the exact reciprocity pairing consumed
by the finite tensor certificate. Every column and denominator is preserved. -/
public theorem RealStem.tensorCoefficient_eq_tableTensor {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) (i j k : Fin 10) :
    s.tensorCoefficient i j k = tableTensor s.row d.rootFive d.rootNineteen i j k := by
  unfold RealStem.tensorCoefficient tableTensor
  apply Finset.sum_congr rfl
  intro c hc
  have hc' : c ≠ 9 := (Finset.mem_erase.mp hc).1
  rw [s.value_eq_edgeTerms i c hc', s.value_eq_edgeTerms j c hc', d.values, d.values]

/-- A tensor multiplicity cannot yield a negative integer, even after
scaling. This is the positivity obstruction used by the finite certificate. -/
public theorem RealStem.scaled_tableTensor_ne_negative {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) (hpos : s.TensorPositive) (i j k : Fin 10)
    (scale n : ℕ) (hn : 0 < n) :
    (scale : ℂ) * tableTensor s.row d.rootFive d.rootNineteen i j k ≠ -(n : ℂ) := by
  obtain ⟨m, hm⟩ := hpos i j k
  rw [← s.tensorCoefficient_eq_tableTensor, hm]
  intro h
  have hreal : (scale : ℝ) * (m : ℝ) = -(n : ℝ) := by
    simpa using congrArg Complex.re h
  have hnonneg : 0 ≤ (scale : ℝ) * (m : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  linarith

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree
