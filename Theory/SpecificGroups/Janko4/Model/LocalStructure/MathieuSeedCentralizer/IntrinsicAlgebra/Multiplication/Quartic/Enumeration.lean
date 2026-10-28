module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure
public import Mathlib.Data.List.Lex
public import Mathlib.Order.Fin.Basic

/-!
# The exact published ordering of the quartic coordinates

We check adjacent entries of each tuple and adjacent tuples of the actual
`quarticTuples`. Transitivity proves the full strict lexicographic ordering.
For completeness, the usual binomial-count formula gives the position of an
increasing quadruple; its lookup is checked against the published array.
Thus both the order and the unique occurrence of every increasing tuple are
certified, not merely the size of an auxiliary family.

The array comes from `SeedCentralizer/explore.py`, as documented in
`IntrinsicAlgebra/source/README.md`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

set_option maxRecDepth 100000 in
theorem quarticTuples_strictMono (q : Fin 210) : StrictMono (quarticTuples.get q) := by
  have h : ∀ q : Fin 210, ∀ i : Fin 3,
      quarticTuples.get q i.castSucc < quarticTuples.get q i.succ := by decide +kernel
  exact Fin.strictMono_iff_lt_succ.mpr (h q)

set_option maxRecDepth 100000 in
private lemma quarticTuples_lists_strictMono :
    StrictMono (fun q : Fin 210 => List.ofFn (quarticTuples.get q)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have h : ∀ q : Fin 209, List.Lex (· < ·)
      (List.ofFn (quarticTuples.get q.castSucc))
      (List.ofFn (quarticTuples.get q.succ)) := by decide +kernel
  exact h

/-- The displayed positions, not an unspecified reordering, are lexicographic. -/
theorem quarticTuples_lex {q r : Fin 210} (h : q < r) :
    List.Lex (· < ·) (List.ofFn (quarticTuples.get q))
      (List.ofFn (quarticTuples.get r)) :=
  quarticTuples_lists_strictMono h

theorem quarticTuples_injective : Function.Injective quarticTuples.get := by
  intro q r h
  exact quarticTuples_lists_strictMono.injective (congrArg List.ofFn h)

/-- A lookup witness obtained by counting the earlier increasing tuples. The
modulus only makes this a total function on arbitrary, possibly repeated inputs. -/
private def quarticIndex (a b c d : Fin 10) : Fin 210 :=
  ⟨((210 - Nat.choose (10-a.val) 4) +
    (Nat.choose (9-a.val) 3 - Nat.choose (10-b.val) 3) +
    (Nat.choose (9-b.val) 2 - Nat.choose (10-c.val) 2) + (d.val-c.val-1)) % 210,
    Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
private lemma quarticIndex_lookup : ∀ a b c d : Fin 10,
    a < b → b < c → c < d →
      quarticTuples.get (quarticIndex a b c d) = ![a, b, c, d] := by
  decide +kernel

/-- Every strictly increasing tuple appears exactly once in the published array. -/
theorem quarticTuples_existsUnique (t : Fin 4 → Fin 10) (ht : StrictMono t) :
    ∃! q : Fin 210, quarticTuples.get q = t := by
  have he : quarticTuples.get (quarticIndex (t 0) (t 1) (t 2) (t 3)) = t := by
    rw [quarticIndex_lookup (t 0) (t 1) (t 2) (t 3)
      (ht (by decide)) (ht (by decide)) (ht (by decide))]
    ext i
    fin_cases i <;> rfl
  exact ⟨_, he, fun q hq => quarticTuples_injective (hq.trans he.symm)⟩

theorem quarticTuples_mem_iff (t : Fin 4 → Fin 10) :
    (∃ q : Fin 210, quarticTuples.get q = t) ↔ StrictMono t := by
  constructor
  · rintro ⟨q, rfl⟩
    exact quarticTuples_strictMono q
  · intro h
    exact (quarticTuples_existsUnique t h).exists

/-- Calibration retains exactly the published coefficient word. -/
theorem quarticPacked_eq :
    quarticPacked = 0x1d74239119236cff2cabddd5c0da56a4bf066e6556c887deab2d := rfl

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
