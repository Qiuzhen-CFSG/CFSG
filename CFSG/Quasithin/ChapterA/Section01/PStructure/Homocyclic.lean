module

public import Theory.GroupTheory.PGroup.HomocyclicPrimeAction

/-!
# The homocyclic fixation assertion of A.1.30

For a prime `p > 3`, every order-`p` automorphism of a group isomorphic to
`C(p²) × C(p²)` fixes its omega subgroup pointwise. The proof uses the
actual coordinate isomorphism and the displacement/binomial calculation.
The consequent exclusion of an `SL₂(p)` subgroup is assembled by the parent
p-group structure module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma A.1.30, printed p.27.
-/

namespace CFSG.Quasithin.ChapterA

/-- The first assertion of A.1.30, with the concrete homocyclic isomorphism. -/
public theorem homocyclic_order_prime_fixes_omega {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P] (hp : 3 < p)
    (e : P ≃* (Multiplicative (ZMod (p ^ 2)) × Multiplicative (ZMod (p ^ 2))))
    (a : MulAut P) (ha : orderOf a = p) : ∀ x ∈ omega₁ P (p := p), a x = x := by
  apply HomocyclicPrimeAction.fixes_omega_of_equiv hp e a
  simpa only [ha] using pow_orderOf_eq_one a

end CFSG.Quasithin.ChapterA
