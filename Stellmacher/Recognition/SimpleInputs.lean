module

public import FeitThompson.FinalTheorem
public import Theory.PPrimeCore

/-!
# Local-classification inputs for nonsolvable simple groups

A finite nonsolvable simple group has even order and trivial two-core and
two-prime-core. This supplies the elementary ambient hypotheses needed when
applying Stellmacher's local classification to a simple group.

The odd-order theorem excludes odd cardinality. Simplicity makes each normal
core either trivial or the whole group: the latter possibility would make the
group nilpotent for the two-core, or give it odd order for the two-prime-core.

Source: the simple-group setting in the introduction to
`refs/latex/stellmacher-n-group.tex`, together with the proved Feit–Thompson
odd-order theorem and the standard normal-subgroup criterion for simplicity.
-/

namespace Stellmacher.Recognition

/-- A nonsolvable finite simple group has the ambient hypotheses for the local
classification: even order and trivial two-core and two-prime-core. -/
public theorem simple_nonsolvable_inputs
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hNonsolvable : ¬ Group.IsSolvable G) :
    Even (Nat.card G) ∧ pCore 2 G = ⊥ ∧ pPrimeCore 2 G = ⊥ := by
  have hEven : Even (Nat.card G) := by
    by_contra hOdd
    exact hNonsolvable (odd_order_theorem G (Nat.not_even_iff_odd.mp hOdd))
  refine ⟨hEven, ?_, ?_⟩
  · rcases (pCore_normal (p := 2) (G := G)).eq_bot_or_eq_top with hBot | hTop
    · exact hBot
    · have hNilpotent := pCore_isNilpotent (p := 2) (G := G)
      rw [hTop] at hNilpotent
      have : Group.IsNilpotent G := Group.isNilpotent_top.mp hNilpotent
      exact (hNonsolvable inferInstance).elim
  · rcases (pPrimeCore_normal (p := 2) (G := G)).eq_bot_or_eq_top with hBot | hTop
    · exact hBot
    · have hCoprime := pPrimeCore_coprime_card (p := 2) (G := G)
      rw [hTop, Subgroup.card_top] at hCoprime
      exact ((Nat.prime_two.coprime_iff_not_dvd.mp hCoprime) hEven.two_dvd).elim

end Stellmacher.Recognition
