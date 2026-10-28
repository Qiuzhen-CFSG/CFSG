module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.Words
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Prime obstructions outside the two marked stabilizers

Every proposed representative either preserves the marked octad or trio, or
a positive word in it and the native Sylow generators has a point of period
5, 7, 11, or 23. Checking a single prime cycle suffices: that prime divides
the word's order, and hence the order of any subgroup containing its letters.
The two permitted subgroup orders have none of these prime divisors.

This proves the finite representative calculation. Exhaustive coverage of
native M₂₄ by those representatives remains the separate `Covers` obligation.
In particular no maximal-subgroup list is silently treated as coverage.

Source: Aschbacher–Smith, printed p.511; GLS3 Table 5.3e; Aschbacher,
*Sporadic Groups*, Chapter 7, §20. The untrusted word search is in `source/`.
-/

public section
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
open SylowNormalizer
set_option maxRecDepth 1000000

private theorem checks : ∀ i : Fin 510,
    representativePerm i • markedOctadPoints = markedOctadPoints ∨
    representativePerm i • markedTrioParts = markedTrioParts ∨
    (obstruction i (obstructionPoint i) ≠ obstructionPoint i ∧
      (obstruction i ^ 5) (obstructionPoint i) = obstructionPoint i) ∨
    (obstruction i (obstructionPoint i) ≠ obstructionPoint i ∧
      (obstruction i ^ 7) (obstructionPoint i) = obstructionPoint i) ∨
    (obstruction i (obstructionPoint i) ≠ obstructionPoint i ∧
      (obstruction i ^ 11) (obstructionPoint i) = obstructionPoint i) ∨
    (obstruction i (obstructionPoint i) ≠ obstructionPoint i ∧
      (obstruction i ^ 23) (obstructionPoint i) = obstructionPoint i) := by
  decide +kernel

private theorem prime_dvd_orderOf_of_cycle {p : ℕ} [Fact (Nat.Prime p)]
    (g : Equiv.Perm (Fin 24)) (x : Fin 24)
    (hfix : g x ≠ x) (hper : (g ^ p) x = x) : p ∣ orderOf g := by
  have he : Function.minimalPeriod g x = p :=
    Function.minimalPeriod_eq_prime hper hfix
  rw [← he]
  apply Function.IsPeriodicPt.minimalPeriod_dvd
  change (g ^ orderOf g) x = x
  rw [pow_orderOf_eq_one]
  rfl

theorem representative_alternative (i : Fin 510) :
    representativePerm i • markedOctadPoints = markedOctadPoints ∨
    representativePerm i • markedTrioParts = markedTrioParts ∨
    5 ∣ orderOf (obstruction i) ∨ 7 ∣ orderOf (obstruction i) ∨
    11 ∣ orderOf (obstruction i) ∨ 23 ∣ orderOf (obstruction i) := by
  rcases checks i with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right; left
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact prime_dvd_orderOf_of_cycle _ _ h.1 h.2
  · right; right; right; left
    let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact prime_dvd_orderOf_of_cycle _ _ h.1 h.2
  · right; right; right; right; left
    let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
    exact prime_dvd_orderOf_of_cycle _ _ h.1 h.2
  · right; right; right; right; right
    let _ : Fact (Nat.Prime 23) := ⟨by decide⟩
    exact prime_dvd_orderOf_of_cycle _ _ h.1 h.2

theorem representative_stabilizes (H : Subgroup M24) (hS : candidate ≤ H)
    (hcard : Nat.card H = 9216 ∨ Nat.card H = 27648)
    (i : Fin 510) (hi : representativePerm i ∈ H.map M24.subtype) :
    representativePerm i • markedOctadPoints = markedOctadPoints ∨
    representativePerm i • markedTrioParts = markedTrioParts := by
  have hd : orderOf (obstruction i) ∣ Nat.card H :=
    ((H.map M24.subtype).orderOf_dvd_natCard
      (localWord_mem H hS i hi (obstructionWords i))).trans
        (H.card_map_dvd M24.subtype)
  rcases representative_alternative i with ho | ht | h | h | h | h
  · exact Or.inl ho
  · exact Or.inr ht
  all_goals have hdiv := h.trans hd; rcases hcard with hcard | hcard <;> rw [hcard] at hdiv <;>
    norm_num at hdiv

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
