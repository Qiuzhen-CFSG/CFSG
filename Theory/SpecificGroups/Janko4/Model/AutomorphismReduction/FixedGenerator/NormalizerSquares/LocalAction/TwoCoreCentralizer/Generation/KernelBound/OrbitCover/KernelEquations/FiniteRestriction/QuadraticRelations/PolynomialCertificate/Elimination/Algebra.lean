module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Table
/-!
# Boolean algebra for the polynomial elimination certificate

Affine expressions are lists of variables and constants. Their products are
encoded in the shared upper triangular monomial order. The evaluation lemmas
explicitly reduce diagonal squares with `square_eq_self` and account for
commutativity when sorting the two variables of a monomial.

This is the soundness layer for the ideal identities derived from the Gaussian
witnesses in `../source/witnesses.json`; see that directory's README for provenance.
-/

@[expose] public section
set_option maxRecDepth 10000
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.Elimination

private theorem slot_separated : ∀ (i u : Fin 125), i < u → slot i 124 < slot u u := by
  decide +kernel

private theorem slot_lower (i j : Fin 125) (h : i ≤ j) : slot i i ≤ slot i j := by
  unfold slot
  omega

private theorem slot_upper (i j : Fin 125) : slot i j ≤ slot i 124 := by
  unfold slot
  omega

private theorem slot_pos (i j : Fin 125) (h : i ≤ j) : 0 < slot i j := by
  have hd : ∀ i : Fin 125, 0 < slot i i := by decide +kernel
  exact lt_of_lt_of_le (hd i) (slot_lower i j h)

private theorem slot_inj (i j u v : Fin 125) (hij : i ≤ j) (huv : u ≤ v) :
    slot i j = slot u v ↔ i = u ∧ j = v := by
  constructor
  · intro h
    have hi : i = u := by
      rcases lt_trichotomy i u with hi | hi | hi
      · have := lt_of_le_of_lt (slot_upper i j) (slot_separated i u hi)
        have := lt_of_lt_of_le this (slot_lower u v huv)
        omega
      · exact hi
      · have := lt_of_le_of_lt (slot_upper u v) (slot_separated u i hi)
        have := lt_of_lt_of_le this (slot_lower i j hij)
        omega
    subst u
    refine ⟨rfl, Fin.ext ?_⟩
    unfold slot at h
    have := hij
    have := huv
    simp only [Fin.le_iff_val_le_val] at *
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem eval_monomial (i j : Fin 125) (hij : i ≤ j) (x : Coefficients) :
    eval (2 ^ slot i j) x = x i * x j := by
  have h0 : slot i j ≠ 0 := ne_of_gt (slot_pos i j hij)
  unfold eval
  simp only [bit, Nat.testBit_two_pow, decide_eq_true_eq, h0, if_false, zero_add]
  have hc (u v : Fin 125) :
      (if u ≤ v then (if slot i j = slot u v then (1 : ZMod 2) else 0) * (x u * x v)
        else 0) = if u = i then if v = j then x i * x j else 0 else 0 := by
    by_cases huv : u ≤ v
    · have heq : slot i j = slot u v ↔ u = i ∧ v = j := by
        rw [slot_inj i j u v hij huv]
        simp only [eq_comm]
      simp only [huv, if_true, heq]
      by_cases hui : u = i <;> by_cases hvj : v = j <;> simp [hui, hvj]
    · by_cases hui : u = i <;> by_cases hvj : v = j <;> simp_all
  simp_rw [hc]
  simp

private theorem eval_one (x : Coefficients) : eval 1 x = 1 := by
  have hc (i j : Fin 125) :
      (if i ≤ j then bit 1 (slot i j) * (x i * x j) else 0) = 0 := by
    by_cases h : i ≤ j
    · have hn : 0 ≠ slot i j := (ne_of_gt (slot_pos i j h)).symm
      change (if i ≤ j then bit (2 ^ 0) (slot i j) * (x i * x j) else 0) = 0
      simp only [h, if_true, bit, Nat.testBit_two_pow, decide_eq_true_eq, hn,
        if_false, zero_mul]
    · simp [h]
  unfold eval
  simp_rw [hc]
  simp [bit]

/-- An affine factor is a list of variables, with `none` denoting the constant one.
Repeated terms cancel because the coefficient field has characteristic two. -/
abbrev Affine := List (Option (Fin 125))

def atomValue (x : Coefficients) : Option (Fin 125) → ZMod 2
  | none => 1
  | some i => x i

def atomRow : Option (Fin 125) → ℕ
  | none => 1
  | some i => 2 ^ slot i i

def pairRow : Option (Fin 125) → Option (Fin 125) → ℕ
  | none, b => atomRow b
  | some i, none => atomRow (some i)
  | some i, some j => if i ≤ j then 2 ^ slot i j else 2 ^ slot j i

def affineRow (a : Affine) : ℕ := xorList (a.map atomRow)

def productRow (a b : Affine) : ℕ :=
  xorList (a.map (fun i => xorList (b.map (pairRow i))))

theorem eval_atom (a : Option (Fin 125)) (x : Coefficients) :
    eval (atomRow a) x = atomValue x a := by
  cases a with
  | none => exact eval_one x
  | some i => exact (eval_monomial i i le_rfl x).trans (square_eq_self (x i))

theorem eval_pair (a b : Option (Fin 125)) (x : Coefficients) :
    eval (pairRow a b) x = atomValue x a * atomValue x b := by
  cases a with
  | none => simpa [pairRow, atomValue] using eval_atom b x
  | some i =>
    cases b with
    | none => simpa [pairRow, atomValue] using eval_atom (some i) x
    | some j =>
      dsimp [pairRow, atomValue]
      split
      · exact eval_monomial _ _ ‹_› x
      · rw [eval_monomial j i (le_of_not_ge ‹_›) x, mul_comm]

theorem eval_affine (a : Affine) (x : Coefficients) :
    eval (affineRow a) x = (a.map (atomValue x)).sum := by
  simp only [affineRow, eval_xorList, List.map_map, Function.comp_def, eval_atom]

theorem eval_product (a b : Affine) (x : Coefficients) :
    eval (productRow a b) x = eval (affineRow a) x * eval (affineRow b) x := by
  have inner (i : Option (Fin 125)) :
      eval (xorList (b.map (pairRow i))) x = atomValue x i * eval (affineRow b) x := by
    rw [eval_xorList, eval_affine, List.map_map]
    simp only [Function.comp_def]
    simp only [eval_pair]
    induction b with
    | nil => simp
    | cons j b ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]
  rw [productRow, eval_xorList, List.map_map]
  simp only [Function.comp_def]
  simp only [inner]
  simp only [eval_affine]
  induction a with
  | nil => simp
  | cons i a ih => simp only [List.map_cons, List.sum_cons, add_mul, ih]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.Elimination
