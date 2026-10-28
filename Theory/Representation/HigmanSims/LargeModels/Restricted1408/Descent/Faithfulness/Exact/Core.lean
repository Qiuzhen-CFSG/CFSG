module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Core
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# The source centralizer subgroup in the abstract HS presentation

The five words defining H in ATLAS HSG1-P1.M centralize the first marked
involution. Odd commutator orders produce the two conjugating words; even
commutator order produces the two half powers. All statements hold in the
abstract thirteen-relator group, without a finiteness or faithfulness premise.

For the subsequent coset certificate we work directly over the centralizer,
which contains H. Four auxiliary letters name these literal words and introduce
only proved naming identities. Source: the retained
`../../../source/HSG1-P1.M`, with its attribution and multiplication conventions.
-/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact

private theorem inv_eq {G : Type*} [Group G] (a : G) (ha : a ^ 2 = 1) : a⁻¹ = a := by
  apply inv_eq_of_mul_eq_one_right
  simpa [pow_two] using ha

private theorem even_commutes {G : Type*} [Group G] (a b : G) (ha : a ^ 2 = 1)
    (n : Nat) (hr : (a⁻¹ * b⁻¹ * a * b) ^ (2*n) = 1) :
    (a⁻¹ * b⁻¹ * a * b) ^ n * a = a * (a⁻¹ * b⁻¹ * a * b) ^ n := by
  let c := a⁻¹ * b⁻¹ * a * b
  have hc : a⁻¹ * c * a = c⁻¹ := by
    have haa : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, ← pow_two, ha, inv_one]
    simp only [c, ← mul_assoc, haa, one_mul]
    simp only [mul_inv_rev, inv_inv, inv_eq a ha, mul_assoc]
  have hcn : a⁻¹ * c^n * a = (c^n)⁻¹ := by
    rw [← inv_pow, ← hc]
    simpa using (conj_pow (a := a⁻¹) (b := c) (i := n)).symm
  have he : (c^n)⁻¹ = c^n := inv_eq _ (by rw [← pow_mul]; simpa [Nat.mul_comm, c] using hr)
  rw [he] at hcn
  calc
    c^n * a = a * (a⁻¹ * c^n * a) := by group
    _ = a * c^n := by rw [hcn]

private theorem odd_commutes {G : Type*} [Group G] (a b : G) (ha : a ^ 2 = 1)
    (n : Nat) (hr : (a⁻¹ * b⁻¹ * a * b) ^ (2*n+1) = 1) :
    (b * (a⁻¹ * b⁻¹ * a * b) ^ n) * a = a * (b * (a⁻¹ * b⁻¹ * a * b) ^ n) := by
  let c := a⁻¹ * b⁻¹ * a * b
  have hc : a⁻¹ * c * a = c⁻¹ := by
    have haa : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, ← pow_two, ha, inv_one]
    simp only [c, ← mul_assoc, haa, one_mul]
    simp only [mul_inv_rev, inv_inv, inv_eq a ha, mul_assoc]
  have hcn : a⁻¹ * c^n * a = (c^n)⁻¹ := by
    rw [← inv_pow, ← hc]
    simpa using (conj_pow (a := a⁻¹) (b := c) (i := n)).symm
  have he : c^n * c * c^n = 1 := by
    rw [← pow_succ, ← pow_add]
    convert hr using 1
    dsimp [c]
    congr 1
    omega
  have hinv : (c^n)⁻¹ = c * c^n := by
    apply inv_eq_of_mul_eq_one_right
    simpa [mul_assoc] using he
  rw [hinv] at hcn
  calc
    b * c^n * a = b * a * (a⁻¹ * c^n * a) := by group
    _ = b * a * (c * c^n) := by rw [hcn]
    _ = (b * a * c) * c^n := (mul_assoc _ _ _).symm
    _ = a * (b * c^n) := by
      have hbc : b * a * c = a * b := by dsimp [c]; group
      rw [hbc, mul_assoc]


private theorem comm_inverse_pow {G : Type*} [Group G] (a b : G) (n : Nat)
    (h : (a⁻¹ * b⁻¹ * a * b)^n = 1) : (a⁻¹ * (b⁻¹)⁻¹ * a * b⁻¹)^n = 1 := by
  have he : a⁻¹ * (b⁻¹)⁻¹ * a * b⁻¹ = b * (a⁻¹ * b⁻¹ * a * b)⁻¹ * b⁻¹ := by group
  rw [he, conj_pow, inv_pow, h, inv_one, mul_one, mul_inv_cancel]

@[expose] public def extendedPair {G : Type*} [Group G] (a b : G) : Fin 6 → G :=
  ![a, b, b * (a⁻¹ * b⁻¹ * a * b)^2,
    (b*a*b) * (a⁻¹ * (b*a*b)⁻¹ * a * (b*a*b)),
    (a⁻¹ * (b^2)⁻¹ * a * b^2)^3,
    (a⁻¹ * (b⁻¹^2)⁻¹ * a * b⁻¹^2)^3]

@[expose] public def traceGenerator : Fin 6 → Universal :=
  extendedPair (generator false) (generator true)

@[expose] public def centralizer : Subgroup Universal :=
  Subgroup.centralizer {generator false}

private theorem square_a : generator false ^ 2 = 1 := by
  simpa [word, relatorLetters, letter, pow_succ, mul_assoc] using universal_word 0
private theorem comm_fifth :
    ((generator false)⁻¹ * (generator true)⁻¹ * generator false * generator true)^5 = 1 := by
  simpa [word, relatorLetters, letter, pow_succ, mul_assoc] using universal_word 4
private theorem comm_third :
    ((generator false)⁻¹ * (generator true * generator false * generator true)⁻¹ *
      generator false * (generator true * generator false * generator true))^3 = 1 := by
  simpa [word, relatorLetters, letter, pow_succ, mul_assoc] using universal_word 5
private theorem comm_sixth :
    ((generator false)⁻¹ * (generator true ^ 2)⁻¹ * generator false * generator true ^ 2)^6 = 1 := by
  simpa [word, relatorLetters, letter, pow_succ, mul_assoc] using universal_word 6

public theorem source_generator_mem (i : Fin 6) (hi : i ≠ 1) :
    traceGenerator i ∈ centralizer := by
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ rfl
  fin_cases i
  · rfl
  · exact (hi rfl).elim
  · exact (odd_commutes _ _ square_a 2 comm_fifth).symm
  · simpa [traceGenerator, extendedPair] using (odd_commutes _ _ square_a 1 comm_third).symm
  · exact (even_commutes _ _ square_a 3 comm_sixth).symm
  · have h := comm_inverse_pow (generator false) (generator true^2) 6 comm_sixth
    simp only [← inv_pow] at h
    exact (even_commutes _ _ square_a 3 h).symm


open Subgroup.CosetWordCertificate

@[expose] public def tracePair {G : Type*} [Group G] (a b : G) (n : Nat) : G :=
  extendedPair a b ⟨n % 6, Nat.mod_lt _ (by decide)⟩
@[expose] public def certGenerator : Nat → Universal :=
  tracePair (generator false) (generator true)
@[expose] public def sourceLetter : Fin 4 → Letter Nat :=
  ![(0, true), (1, true), (0, false), (1, false)]
@[expose] public def sourceWords (r : Nat) : Word Nat :=
  if h : r < 13 then (relatorLetters ⟨r, h⟩).map sourceLetter
  else if r = 13 then [(1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (2, false)]
  else if r = 14 then [(1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (3, false)]
  else if r = 15 then [(0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (4, false)]
  else if r = 16 then [(0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (5, false)]
  else []

public theorem eval_sourceLetters {G : Type*} [Group G] (a b : G) (i : Fin 13) :
    eval (tracePair a b) ((relatorLetters i).map sourceLetter) = word a b i := by
  simp only [eval, FreeGroup.lift_mk, List.map_map, word]
  congr 2
  funext j
  fin_cases j <;> simp [sourceLetter, tracePair, extendedPair, letter]

public theorem sourceWords_valid (r : Nat) : eval certGenerator (sourceWords r) = 1 := by
  by_cases h : r < 13
  · rw [sourceWords, dif_pos h]
    exact (eval_sourceLetters _ _ ⟨r, h⟩).trans (universal_word ⟨r, h⟩)
  · by_cases h13 : r = 13
    · subst r
      simp [sourceWords, certGenerator, tracePair, extendedPair, eval_cons, pow_succ, mul_assoc]
    · by_cases h14 : r = 14
      · subst r
        simp [sourceWords, certGenerator, tracePair, extendedPair, eval_cons, pow_succ, mul_assoc]
      · by_cases h15 : r = 15
        · subst r
          simp [sourceWords, certGenerator, tracePair, extendedPair, eval_cons, pow_succ, mul_assoc]
        · by_cases h16 : r = 16
          · subst r
            simp [sourceWords, certGenerator, tracePair, extendedPair, eval_cons, pow_succ, mul_assoc]
          · simp [sourceWords, h, h13, h14, h15, h16]

@[expose] public def allowed (a : Letter Nat) : Bool :=
  decide (a = (0, true) ∨ a = (2, true) ∨ a = (3, true) ∨
    a = (4, true) ∨ a = (5, true))

public theorem allowed_mem (a : Letter Nat) (h : allowed a = true) :
    eval certGenerator [a] ∈ centralizer := by
  have ha : a = (0, true) ∨ a = (2, true) ∨ a = (3, true) ∨
      a = (4, true) ∨ a = (5, true) := by simpa [allowed] using h
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact source_generator_mem 0 (by decide)
  · exact source_generator_mem 2 (by decide)
  · exact source_generator_mem 3 (by decide)
  · exact source_generator_mem 4 (by decide)
  · exact source_generator_mem 5 (by decide)

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact
