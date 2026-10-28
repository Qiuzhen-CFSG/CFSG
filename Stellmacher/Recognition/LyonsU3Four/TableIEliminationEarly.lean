module

public import Stellmacher.Recognition.LyonsU3Four.TableIPatterns
public import Stellmacher.Recognition.LyonsU3Four.TableIHArithmetic
public import Stellmacher.Recognition.LyonsU3Four.TableIEliminationADG
public import Stellmacher.Recognition.LyonsU3Four.TableIEliminationB
public import Stellmacher.Recognition.LyonsU3Four.TableIEliminationCEF
public import Stellmacher.Recognition.LyonsU3Four.TableIEliminationJKL
public import Stellmacher.Recognition.LyonsU3Four.TableISignedDegreeTransport

/-!
# Early eliminations in Lyons's Table I

The eleven cases A–H and J–L admit no signed integer degrees satisfying the
degree, positive order, and prime constraints. Both Z₁/Z₂ variants of A–E are
included. The imported case eliminations derive their equations and bounds
from the explicit matrices, retaining signed multiplicity nonnegativity and
congruence and proving row separation wherever a prime bound is used.

Case H is excluded directly from the thirteen displayed rows. The first five
rows are Z₄; all three repeated final rows are retained. Signed Galois symmetry
forces the repeated degree labels. Evaluating the order-four weighted column
and ordinary degree orthogonality gives (H1) and (H2), which contradict the
signed multiplicity constraints.

`tableI_early_impossible` combines all eleven canonical case eliminations.
`tableI_early_impossible_of_signed_matrix` transports them through an explicit
signed row equivalence. Exhaustive classification remains the responsibility
of the consumer: the unconstrained `TableIPatternWitness.matrix` alone does
not identify a displayed case. Existing H interfaces are preserved.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), Table I pp. 374–377 and eliminations pp. 382–384. Matrix entries were
checked against the page images in
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData
open scoped BigOperators

/-- The thirteen rows of case H, including Z₄ and the repeated rows. -/
@[expose] def tableIHRows : Fin 13 → Fin 6 → ℤ := ![
  ![1,1,0,0,0,0],
  ![1,1,2,1,0,1],
  ![1,1,1,0,1,2],
  ![1,1,0,1,2,1],
  ![1,1,1,2,1,0],
  ![0,2,2,1,2,1],
  ![0,2,1,2,1,2],
  ![-1,1,0,1,0,1],
  ![-1,1,1,0,1,0],
  ![-3,1,1,1,1,1],
  ![0,0,1,1,1,1],
  ![0,0,1,1,1,1],
  ![0,0,1,1,1,1]]

/-- Case H as generalized decomposition data; row zero is principal. -/
@[expose] def tableIHData : GeneralizedDecompositionData (Fin 13) where
  dT j := tableIHRows j 0
  iDz i j := tableIHRows j i.succ

private theorem degree_step (degree : Fin 13 → ℤ) (h : tableIHData.SignedGaloisSymmetry degree)
    (a b : Fin 13)
    (hpos : ∀ k : Fin 13, (tableIHData.dT a = tableIHData.dT k ∧
      ∀ i, tableIHData.iDz i a = tableIHData.iDz (galoisColumn i) k) → k = b)
    (hneg : ∀ k : Fin 13, ¬ (tableIHData.dT a = -tableIHData.dT k ∧
      ∀ i, tableIHData.iDz i a = -tableIHData.iDz (galoisColumn i) k)) :
    degree a = degree b := by
  obtain ⟨σ, hs⟩ := h
  obtain ⟨ε, he, hd, ht, hz⟩ := hs a
  rcases sq_eq_one_iff.mp he with rfl | rfl
  · have hk := hpos (σ a) ⟨by simpa using ht, by simpa using hz⟩
    simpa [hk] using hd
  · exact False.elim (hneg (σ a) ⟨by simpa using ht, by simpa using hz⟩)

/-- Galois invariance gives the repeated degree labels printed in case H. -/
theorem tableIH_galois_degrees (degree : Fin 13 → ℤ) (h : tableIHData.SignedGaloisSymmetry degree) :
    degree 1 = degree 2 ∧ degree 2 = degree 3 ∧ degree 3 = degree 4 ∧
      degree 7 = degree 8 := by
  exact ⟨degree_step degree h 1 2 (by decide) (by decide),
    degree_step degree h 2 3 (by decide) (by decide),
    degree_step degree h 3 4 (by decide) (by decide),
    degree_step degree h 7 8 (by decide) (by decide)⟩

private theorem t_values (j : Fin 13) : tableIHData.dT j = ![1,1,1,1,1,0,0,-1,-1,-3,0,0,0] j := by
  fin_cases j <;> decide

private theorem z_values (j : Fin 13) : tableIHData.zValue j = ![1,5,5,5,5,8,8,3,3,5,4,4,4] j := by
  fin_cases j <;> decide

/-- The actual normalized H matrix admits no degree and order constraints. -/
theorem tableIH_impossible (degree : Fin 13 → ℤ) (hd : tableIHData.DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : tableIHData.OrderConstraints degree g c e) : False := by
  obtain ⟨h12, h23, h34, h78⟩ := tableIH_galois_degrees degree hd.galois_symmetry
  have h2 := hd.orthogonal_t
  have h1 := ho.zero_t
  simp only [columnInner, t_values, Fin.sum_univ_succ] at h2
  simp only [weightedColumn, z_values, t_values, Fin.sum_univ_succ] at h1
  dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at h1 h2
  norm_num [hd.principal_degree, ← h12, ← h23, ← h34, ← h78] at h1 h2
  change 1 + (25/(degree 1:ℚ) + (25/(degree 2:ℚ) +
    (25/(degree 3:ℚ) + (25/(degree 4:ℚ) + (-9/(degree 7:ℚ) +
      (-9/(degree 8:ℚ) + -75/(degree 9:ℚ))))))) = 0 at h1
  change 1 + (degree 1 + (degree 2 + (degree 3 + (degree 4 +
    (-degree 7 + (-degree 8 + -(degree 9*3))))))) = 0 at h2
  rw [← h34, ← h23, ← h12, ← h78] at h1 h2
  have hH1 : 1+100/(degree 1:ℚ)-18/(degree 7:ℚ)-75/(degree 9:ℚ)=0 := by
    linear_combination h1
  have hH2 : 1+4*degree 1-2*degree 7-3*degree 9=0 := by
    linear_combination h2
  have hx := hd.bounds_t1_z5 1 (by decide) (by decide) (by decide)
  have hy := hd.bounds_tneg1_z3 7 (by decide) (by decide) (by decide)
  have hz := hd.bounds_tneg3_z5 9 (by decide) (by decide) (by decide)
  have hm1 := hd.multiplicity_integral 1
  have hm9 := hd.multiplicity_integral 9
  rw [t_values, z_values] at hm1 hm9
  have hmx : (degree 1+75)%64=0 := by
    simpa [Int.ModEq, add_assoc] using hm1
  have hmz : (degree 9-165)%64=0 := by
    simpa [Int.ModEq, add_assoc, sub_eq_add_neg] using hm9
  exact tableI_H_arithmetic _ _ _ hx hy hz hmx hmz hH1 hH2

/-- The original H transcription agrees entry by entry with the canonical catalogue. -/
theorem tableIHRows_eq_catalogue : tableIHRows = tableIMatrix .H () := by
  funext j k
  fin_cases j <;> fin_cases k <;> rfl

/-- The H decomposition data agree with the canonical catalogue. -/
theorem tableIHData_eq_catalogue : tableIHData = tableIData .H () := by
  unfold tableIHData tableIData
  rw [tableIHRows_eq_catalogue]
  rfl

/-- The canonical H matrix is excluded without using the prime constraints. -/
theorem tableIH_catalogue_impossible (degree : Fin (tableIRowCount .H) → ℤ)
    (hd : (tableIData .H ()).DegreeConstraints (tableIPrincipal .H) degree)
    {g c e : ℕ} (ho : (tableIData .H ()).OrderConstraints degree g c e) : False := by
  rw [← tableIHData_eq_catalogue] at hd ho
  exact tableIH_impossible degree hd ho

/-- All eleven early catalogue cases, including both variants of A–E, are
excluded by the signed degree, positive order, and prime constraints. -/
theorem tableI_early_impossible (a : TableICase) (v : a.Variant)
    (ha : a ∈ [TableICase.A, .B, .C, .D, .E, .F, .G, .H, .J, .K, .L])
    {degree : Fin (tableIRowCount a) → ℤ} {g c e : ℕ}
    (hd : (tableIData a v).DegreeConstraints (tableIPrincipal a) degree)
    (ho : (tableIData a v).OrderConstraints degree g c e)
    (hp : (tableIData a v).PrimeConstraints degree g) : False := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tableIA_impossible v degree hd ho hp
  · exact tableIB_impossible v degree hd ho hp
  · exact tableIC_impossible v degree hd ho
  · exact tableID_impossible v degree hd ho hp
  · exact tableIE_impossible v degree hd ho
  · cases v
    exact tableIF_impossible degree hd ho
  · cases v
    exact tableIG_impossible degree hd ho hp
  · cases v
    exact tableIH_catalogue_impossible degree hd ho
  · cases v
    exact tableIJ_impossible degree hd ho hp
  · cases v
    exact tableIK_impossible degree hd ho hp
  · cases v
    exact tableIL_impossible degree hd ho hp

/-- Exclude an early case identified by a signed row equivalence. All three
constraint packages, including row separation, travel with the signed degrees. -/
theorem tableI_early_impossible_of_signed_matrix
    {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    {principal : I} {degree : I → ℤ} {g c z : ℕ}
    (a : TableICase) (v : a.Variant)
    (ha : a ∈ [TableICase.A, .B, .C, .D, .E, .F, .G, .H, .J, .K, .L])
    (e : I ≃ Fin (tableIRowCount a)) (ε : I → ℤ)
    (hε : ∀ j, ε j ^ 2 = 1)
    (hm : ∀ j k, d.tableIRow j k = ε j * tableIMatrix a v (e j) k)
    (he : e principal = tableIPrincipal a)
    (hpat : d.TableIPatternHypotheses principal)
    (hd : d.DegreeConstraints principal degree)
    (ho : d.OrderConstraints degree g c z)
    (hp : d.PrimeConstraints degree g) : False := by
  have hq : tableIMatrix a v (tableIPrincipal a) 0 = 1 := by
    rw [tableIMatrix_principal]
    rfl
  obtain ⟨hd', ho', hp'⟩ := constraints_of_signed_matrix e ε hε hm he
    hpat.principal_dT hq hd ho hp
  exact tableI_early_impossible a v ha hd' ho' hp'

end Stellmacher.Recognition.LyonsU3Four
