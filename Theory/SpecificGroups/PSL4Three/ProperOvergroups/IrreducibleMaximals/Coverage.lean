module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.IrreducibleMaximals.Coverage.Arithmetic
public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.IrreducibleMaximals.Coverage.SeededEnumeration

/-!+# Reduction of irreducible maximal coverage to two prime-order branches

Every nonsolvable subgroup of PSL₄(3) contains an element of order five or
thirteen, by the proved arithmetic and two-prime solvability argument.
If maximal subgroups containing an element of order thirteen are reducible,
the irreducible case reduces to overgroups of an element of order five.

The two overgroup inputs below remain explicit. Neither this reduction nor
the seeded enumeration soundness theorem asserts that a particular finite
enumeration is exhaustive. Those inputs must be proved before the unconditional
coverage theorem can be assembled.

Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals

/-- The two independent prime-order overgroup results suffice for exhaustive
coverage. The order-five or order-thirteen witness is constructed internally. -/
public theorem irreducible_maximal_coverage_of_prime_overgroups
    (hfive : ∀ M : Subgroup PSL, IsCoatom M → ¬ Reducible M →
      ¬ Group.IsSolvable M → (∃ x : M, orderOf x = 5) →
      SymplecticSimilitudes M ∨
        ∃ i : Fin 2, ∃ g : PSL, M = (candidate i).map (MulAut.conj g).toMonoidHom)
    (hthirteen : ∀ M : Subgroup PSL, IsCoatom M →
      (∃ x : M, orderOf x = 13) → Reducible M)
    (M : Subgroup PSL) (hM : IsCoatom M) (hirr : ¬ Reducible M)
    (hnsolv : ¬ Group.IsSolvable M) :
    SymplecticSimilitudes M ∨
      ∃ i : Fin 2, ∃ g : PSL, M = (candidate i).map (MulAut.conj g).toMonoidHom := by
  rcases five_or_thirteen_of_nonsolvable M hnsolv with h5 | h13
  · exact hfive M hM hirr hnsolv h5
  · exact False.elim (hirr (hthirteen M hM h13))

end Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals
