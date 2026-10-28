module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.TransversalData

/-!
# A linear Boolean check for adjacent Sylow coset keys

An exposed Boolean loop checks adjacent keys without rebuilding a dependent
predicate at each step. Its specification converts the computed equality to
the bounded universal assertion. Unlike the unexposed implementation of
`Nat.allLTTR`, this loop reduces in importing modules. All Boolean equalities
are reduced by the kernel.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage

def keyPrefixCheck (a : ℕ) : ℕ → Bool
  | 0 => true
  | b + 1 => decide (a * 5313 + b + 1 < 239085 →
      fastKey (transversalParameter (a * 5313 + b)) <
        fastKey (transversalParameter (a * 5313 + b + 1))) && keyPrefixCheck a b

private theorem keyPrefix_of_check {a n : ℕ} (h : keyPrefixCheck a n = true) :
    ∀ b < n, a * 5313 + b + 1 < 239085 →
      fastKey (transversalParameter (a * 5313 + b)) <
        fastKey (transversalParameter (a * 5313 + b + 1)) := by
  induction n with
  | zero => intro b hb; omega
  | succ n ih =>
    simp only [keyPrefixCheck, Bool.and_eq_true] at h
    intro b hb
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hb) with hb | rfl
    · exact ih h.2 b hb
    · exact of_decide_eq_true h.1

def keyBlockCheck (a : ℕ) : Bool := keyPrefixCheck a 5313

theorem keyBlock_of_check {a : ℕ} (h : keyBlockCheck a = true) : KeyBlock a := by
  intro b hb
  exact keyPrefix_of_check h b.val b.isLt hb

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
