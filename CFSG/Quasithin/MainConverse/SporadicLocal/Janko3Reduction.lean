module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import Theory.SpecificGroups.Janko3.Model.Basic

/-!
# The three J₃ local orders suffice for QT

GLS, *The Classification of the Finite Simple Groups*, Number 3, Table 5.3h
(printed p.269), lists the maximal 2-locals with shapes
`(Q₈ * D₈).A₅`, `4²:GL₂(4)` and `2^(2+4).(S₃ × C₃)`.
Their orders are 1920, 2880 and 1152, all divisors of 5760, whose odd part
is cube-free. Thus an exhaustive cover by conjugates of actual subgroups
with those orders establishes QT.

The coverage and order statements below are explicit outstanding inputs;
this is not a certification of the local table in the degree-6156 carrier.
Unlike a global odd-rank bound, this route is compatible with J₃'s ordinary
three-rank of three. The consumer is Aschbacher–Smith, Theorem 0.1.2(5), p.4.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal

private theorem odd_cube_not_dvd_5760 {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ p ^ 3 ∣ 5760 := by
  intro hd
  have hpd : p ∣ 2 ^ 7 * 3 ^ 2 * 5 :=
    (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rw [hp.dvd_mul, hp.dvd_mul] at hpd
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 := by
    rcases hpd with (h2 | h3) | h5
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h5))
  rcases hcases with rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  all_goals norm_num at hd

/-- The local table's three orders imply QT once coverage of every maximal
2-local in the actual permutation carrier has been established. -/
public theorem j3_quasithin_of_local_cover
    (L : Fin 3 → Subgroup Sporadic.Janko3.Model)
    (h0 : Nat.card (L 0) = 1920) (h1 : Nat.card (L 1) = 2880)
    (h2 : Nat.card (L 2) = 1152)
    (hcover : ∀ M : Subgroup Sporadic.Janko3.Model, IsMaximalTwoLocal M →
      ∃ (i : Fin 3) (g : Sporadic.Janko3.Model),
        M ≤ (L i).map (MulAut.conj g).toMonoidHom) :
    IsQuasithin Sporadic.Janko3.Model := by
  apply quasithin_of_maximal_local_cube_free_cover L hcover
  intro i p hp ho hd
  have hdiv : Nat.card (L i) ∣ 5760 := by
    fin_cases i
    · change Nat.card (L 0) ∣ 5760
      rw [h0]
      decide
    · change Nat.card (L 1) ∣ 5760
      rw [h1]
      decide
    · change Nat.card (L 2) ∣ 5760
      rw [h2]
      decide
  exact odd_cube_not_dvd_5760 hp ho (hd.trans hdiv)

end CFSG.Quasithin.MainConverse.SporadicLocal
