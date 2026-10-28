module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Model
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus.Arithmetic

/-!
# The odd-prime rank obstruction in the concrete unitary-five parabolic

For every even prime power `q ≠ 4`, an odd prime `p ≠ 5` divides `q+1`.
The diagonal matrices `diag(a,a,b,c,(a²bc)⁻¹)`, with `p`-th roots of unity as
parameters, embed an elementary abelian group of order `p³` into the actual
line parabolic of `Model q`. The scalar kernel vanishes because `p ≠ 5`.

This proves the existential rank obstruction used in the last paragraph of
Aschbacher--Smith, *The Classification of Quasithin Groups*, F.1.12 (printed
p. 264), including `q = 2`. Compare the broader all-primes assertion in the
proof of A.2.18 (printed p. 40). The argument here needs no Levi decomposition
and makes no assertion about the 5-primary quotient of the torus.
-/

public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive

/-- A noncentral obstruction prime gives rank three in the concrete line parabolic. -/
theorem Model.leftParabolic_primeRank_ge_of_prime_ne_five
    {q : ℕ} (M : Model q) (hq : 2 ≤ q)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ q + 1) (hne : p ≠ 5) :
    3 ≤ primeRank p M.leftParabolic :=
  Theory.SpecificGroups.UnitaryFive.primeRank_lineParabolic_ge_of_prime_ne_five
    M.form M.matrix M.card hq M.conjugation hp hd hne

/-- The source's existential odd-prime obstruction for all nonexceptional even parameters. -/
theorem exists_odd_prime_parabolic_rank
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (hne : q ≠ 4) (M : Model q) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ q + 1 ∧ 3 ≤ primeRank p M.leftParabolic := by
  obtain ⟨p, hp, ho, hd, hp5⟩ :=
    Theory.SpecificGroups.UnitaryFive.exists_odd_prime_ne_five_dvd_succ hq heven hne
  exact ⟨p, hp, ho, hd,
    M.leftParabolic_primeRank_ge_of_prime_ne_five hq.one_lt hp hd hp5⟩

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive
