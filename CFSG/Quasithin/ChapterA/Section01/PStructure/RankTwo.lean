module
public import Theory.ElementaryAbelian.PrimePlane
public import Theory.GroupTheory.PGroup.ExponentPrimeRankTwoOrder
public import Theory.SpecificGroups.HeisenbergPrime.Recognition

/-!
# The concrete models in A.1.24

An abelian exponent-p group of prime rank two is the elementary plane.
In the nonabelian case, the rank and class assumptions bound the order by
p³, noncommutativity forces equality, and Heisenberg normal-form recognition
supplies a genuine isomorphism and extraspeciality. The final theorem
discharges the order bound from the original exponent, rank and class
hypotheses.

Source: Aschbacher–Smith, Lemma A.1.24, printed p.25. The parent module
PStructure proves the exponent consequence of the first-omega hypothesis.
This descendant does not import that parent.
-/

namespace CFSG.Quasithin.ChapterA

private theorem nonabelian_card_prime_cube_of_bound {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (hn : ¬ IsMulCommutative P) (hbound : Nat.card P ≤ p ^ 3) :
    Nat.card P = p ^ 3 := by
  obtain ⟨n, hncard⟩ := hP.exists_card_eq
  have hnle : n ≤ 3 :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (hncard ▸ hbound)
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · let : IsCyclic P := isCyclic_of_card_dvd_prime (p := p) (by simp [hncard])
    exact (hn inferInstance).elim
  · let : IsCyclic P := isCyclic_of_card_dvd_prime (p := p) (by simp [hncard])
    exact (hn inferInstance).elim
  · exact (hn (IsPGroup.isMulCommutative_of_card_eq_prime_sq hncard)).elim
  · exact hncard

/-- The concrete classification with an explicit order bound.
The two alternatives include actual group equivalences and their orders. -/
public theorem rankTwo_models_of_card_le_prime_cube {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P] (hp : p ≠ 2) (hP : IsPGroup p P)
    (hexp : Monoid.exponent P = p) (hrank : primeRank p P = 2)
    (hclass : _root_.commutator P ≤ Subgroup.center P)
    (hbound : Nat.card P ≤ p ^ 3) :
    (Nat.card P = p ^ 2 ∧
      Nonempty (P ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) ∨
    (Nat.card P = p ^ 3 ∧ IsExtraspecial p P ∧
      Nonempty (P ≃* HeisenbergPrime p)) := by
  classical
  have hpow (x : P) : x ^ p = 1 := by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one x
  by_cases hab : IsMulCommutative P
  · let : IsElementaryAbelian p P := {
      toIsMulCommutative := hab
      exponent_dvd_p := hexp ▸ dvd_refl p }
    exact Or.inl ⟨IsElementaryAbelian.card_eq_prime_sq_of_primeRank_two hrank,
      IsElementaryAbelian.nonempty_mulEquiv_plane_of_primeRank_two hrank⟩
  · have hc := nonabelian_card_prime_cube_of_bound hP hab hbound
    exact Or.inr ⟨hc,
      HeisenbergPrime.isExtraspecial_of_card_prime_cube hp hc hpow hclass hab,
      HeisenbergPrime.nonempty_mulEquiv_of_card_prime_cube hc hpow hclass hab⟩

/-- The concrete classification step of A.1.24: an odd-prime p-group of
exponent p, prime rank two and class at most two is the elementary plane
or the prime Heisenberg group. Both alternatives include their orders and
actual group equivalences; the nonabelian alternative is extraspecial. -/
public theorem rankTwo_models {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P] (hp : p ≠ 2) (hP : IsPGroup p P)
    (hexp : Monoid.exponent P = p) (hrank : primeRank p P = 2)
    (hclass : _root_.commutator P ≤ Subgroup.center P) :
    (Nat.card P = p ^ 2 ∧
      Nonempty (P ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) ∨
    (Nat.card P = p ^ 3 ∧ IsExtraspecial p P ∧
      Nonempty (P ≃* HeisenbergPrime p)) :=
  rankTwo_models_of_card_le_prime_cube hp hP hexp hrank hclass
    (hP.card_le_prime_cube_of_exponent_prime_rank_two hp hexp hrank hclass)

end CFSG.Quasithin.ChapterA
