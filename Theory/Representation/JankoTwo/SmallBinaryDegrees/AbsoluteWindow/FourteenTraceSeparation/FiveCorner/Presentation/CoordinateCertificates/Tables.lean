module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.Checks

/-!
# Reusing verified prefixes in the Hall--Janko polynomial checks

A word code has leading bit one and is extended on the right by its low bit.
`runCode_rec` proves this for the unchanged binary encoding. Strong induction
then validates a sparse table whose code set contains every required binary
parent. `relation_eq_table` checks a polynomial by XOR of its verified table
entries, retaining every term and the actual empty-word value one.

Source: the 87 relations in `FiveCorner/Certificate.lean`, documented in
`Presentation/source/README.md`. No numerical table is assumed correct here.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates

private lemma bits_ne_nil {n : ℕ} (hn : n ≠ 0) : n.bits ≠ [] := by
  induction n using Nat.binaryRec' with
  | zero => exact (hn rfl).elim
  | bit b n h _ =>
    rw [Nat.bits_append_bit n b h]
    exact List.cons_ne_nil _ _

lemma runCode_bit {V : Type*} (ops : Fin 9 → V → V) (v : V)
    (i j : Fin 9) (b : Bool) {n : ℕ} (hn : n ≠ 0) :
    runCode ops v i j (Nat.bit b n) =
      ops (if b then j else i) (runCode ops v i j n) := by
  simp only [runCode, Nat.bits_append_bit n b (fun h => (hn h).elim),
    List.dropLast_cons_of_ne_nil (bits_ne_nil hn), List.reverse_cons,
    List.map_append, List.map_cons, List.map_nil, runWord, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

lemma runCode_rec {V : Type*} (ops : Fin 9 → V → V) (v : V)
    (i j : Fin 9) {n : ℕ} (hn : 2 ≤ n) :
    runCode ops v i j n = ops (if n.testBit 0 then j else i)
      (runCode ops v i j (n / 2)) := by
  have h := runCode_bit ops v i j (Nat.bodd n) (n := Nat.div2 n)
    (by simp only [Nat.div2]; omega)
  rw [Nat.bit_bodd_div2] at h
  exact h

/-- A sparse memoized table is sound if its codes contain their binary parents. -/
lemma runCode_eq_table (i j : Fin 9) (table : ℕ → ℕ) (codes : Finset ℕ)
    (hseed : table 0 = 1 ∧ table 1 = 1)
    (hparent : ∀ n ∈ codes, 2 ≤ n → n / 2 ∈ codes)
    (hstep : ∀ n ∈ codes, 2 ≤ n →
      action (if n.testBit 0 then j else i) (table (n / 2)) = table n)
    (n : ℕ) (hn : n ∈ codes) : runCode action 1 i j n = table n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < 2
    · interval_cases n <;> simp [runCode, runWord, hseed.1, hseed.2]
    · have hbig : 2 ≤ n := by omega
      rw [runCode_rec action 1 i j hbig,
        ih (n / 2) (by omega) (hparent n hn hbig)]
      exact hstep n hn hbig

/-- A verified table reduces a polynomial check to XORs and table lookups. -/
lemma relation_eq_table (r : Certificate.Relation) (table : ℕ → ℕ) (codes : Finset ℕ)
    (hseed : table 0 = 1 ∧ table 1 = 1)
    (hparent : ∀ n ∈ codes, 2 ≤ n → n / 2 ∈ codes)
    (hstep : ∀ n ∈ codes, 2 ≤ n →
      action (if n.testBit 0 then r.second else r.first) (table (n / 2)) = table n)
    (hcodes : ∀ n ∈ r.terms, n ∈ codes) :
    relation r = xorList (r.terms.map table) := by
  unfold relation
  congr 1
  apply List.map_congr_left
  intro n hn
  exact runCode_eq_table r.first r.second table codes hseed hparent hstep n (hcodes n hn)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates
