module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsTwoCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsCenter
public import Theory.GroupAction.ComponentRankAction.OuterPower
public import Theory.SpecificGroups.PSL3.OddPrimeOuterExponent
public import Theory.SpecificGroups.SU3.OddPrimeOuterExponent

/-!
This additive source variant uses `SecondaryActionData` and preserves the
full quotient and central-cover hypotheses without universal radical movement.

# Noncubic source primes in odd-prime ternary models

Every automorphism of PSL₃(r) or PSU₃(r), r an odd prime, has sixth
power inner. A source torus prime other than three therefore cannot have
component rank two: the outside actor would be absorbed by the component.
The ordinary-component reduction uses the literal ambient two-core quotient
and its full component model. No centrality of the original two-core is used.

The determinant exponents also force r ≡ 1 modulo three in the linear
case and r ≡ −1 in the unitary case at cubic rank two. The cubic-center
exclusion discharges centerlessness for these congruences. The explicit
centerless premise in the noncubic theorem is discharged by the catalogue in `NonblockSecondaryCoreEnlargement.SourceSieveModelsPrimeRemainder`.
The remaining binary models and local normalizer inspection remain owned by
qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith A.3.18, pp.51–53; original 4.3.12(2), p.617.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- An outer exponent coprime to a source torus prime forces component rank one. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_inner_power (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p m : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hz : Nat.Coprime p (Nat.card (center (s.component ⧸ pCore 2 s.component))))
    (hcop : Nat.Coprime p m)
    (hpower : ∀ a : MulAut (s.component ⧸ pCore 2 s.component),
      a ^ m ∈ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)) :
    primeRank p s.component = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let K := SecondaryActionData.twoCoreComponent s
  let := SecondaryActionData.twoCoreComponent_normal s
  let e := SecondaryActionData.twoCoreComponentEquiv s
  rcases SecondaryActionData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact hr
  obtain ⟨x, hx, hxn⟩ := SecondaryActionData.exists_twoCore_outside_prime_actor s hp ho hd
  apply False.elim
  apply hxn
  apply Theory.GroupAction.ComponentRankAction.prime_actor_mem_of_full_rank_of_inner_power K
    (by rwa [Nat.card_congr (centerCongr e).toEquiv]) ?_
    ((SecondaryActionData.twoCoreRoot_sqtk s D h).stronglyQuasithin p hp ho) hcop ?_ x hx
  · rw [primeRank_congr p e,
      primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup]
    omega
  · intro a
    have hh := hpower (MulAut.congr e a)
    rw [← map_pow, ← MulAut.map_innerSubgroup_congr e] at hh
    obtain ⟨b, hb, he⟩ := hh
    exact ((MulAut.congr e).injective he) ▸ hb

private theorem simple_of_center_bot {J : Type*} [Group J] [IsQuasisimple J]
    (hz : center J = ⊥) : IsSimpleGroup J := by
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem coprime_six {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) :
    Nat.Coprime p 6 := by
  have h2 : Nat.Coprime p 2 := Nat.coprime_two_right.mpr ho
  have h3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hp3 ((Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hp.ne_one))
  exact h2.mul_right h3

/-- Both odd-prime ternary rows have rank one at every noncubic source prime. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_noncubic_odd_ternary (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p r : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3)
    (hr : r.Prime) (hro : Odd r)
    (hz : center (s.component ⧸ pCore 2 s.component) = ⊥)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r) :
    primeRank p s.component = 1 := by
  let := s.quasisimple
  let := simple_of_center_bot hz
  apply SecondaryActionData.component_primeRank_eq_one_of_inner_power s D h hp ho hd
    (by rw [hz, card_bot]; exact Nat.coprime_one_right p) (coprime_six hp ho hp3)
  intro a
  rcases hm with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, J, hF, hc, ⟨e⟩⟩
  · let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp inferInstance
    let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hh := Matrix.PSL3.odd_prime_sixth_power_inner
      (Group.IsPerfect.not_isSolvable PSL(3,F)) hr hro hF (MulAut.congr e a)
    rw [← map_pow, ← MulAut.map_innerSubgroup_congr e] at hh
    obtain ⟨b, hb, he⟩ := hh
    exact ((MulAut.congr e).injective he) ▸ hb
  · let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      e.isSimpleGroup_congr.mp inferInstance
    have hh := J.odd_prime_sixth_power_inner hr hro hF hc (MulAut.congr e a)
    rw [← map_pow, ← MulAut.map_innerSubgroup_congr e] at hh
    obtain ⟨b, hb, he⟩ := hh
    exact ((MulAut.congr e).injective he) ▸ hb
/-- At cubic rank two the odd linear parameter has the source split congruence. -/
theorem SecondaryActionData.odd_linear_cubic_congruence (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) (hrank : 2 ≤ primeRank 3 s.component)
    {r : ℕ} (hr : r.Prime) (hro : Odd r)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r) : r % 3 = 1 := by
  have hdiv : 3 ∣ r - 1 := by
    by_contra hnot
    have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h hd
    let := s.quasisimple
    let := simple_of_center_bot hz
    have he := SecondaryActionData.component_primeRank_eq_one_of_inner_power s D h
      Nat.prime_three (by decide) hd
      (by rw [hz, card_bot]; decide)
      ((by decide : Nat.Coprime 3 2).mul_right
        (Nat.prime_three.coprime_iff_not_dvd.mpr hnot)) (by
          intro a
          obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
          let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp inferInstance
          let : Group.IsPerfect PSL(3,F) :=
            Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
          have hh := Matrix.PSL3.odd_prime_split_power_inner
            (Group.IsPerfect.not_isSolvable PSL(3,F)) hr hro hF (MulAut.congr e a)
          rw [← map_pow, ← MulAut.map_innerSubgroup_congr e] at hh
          obtain ⟨b, hb, he⟩ := hh
          exact ((MulAut.congr e).injective he) ▸ hb)
    omega
  have hr2 := hr.two_le
  have hh := Nat.mod_eq_zero_of_dvd hdiv
  omega

/-- At cubic rank two the odd unitary parameter has the source nonsplit congruence. -/
theorem SecondaryActionData.odd_unitary_cubic_congruence (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) (hrank : 2 ≤ primeRank 3 s.component)
    {r : ℕ} (hr : r.Prime) (hro : Odd r)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r) : r % 3 = 2 := by
  have hdiv : 3 ∣ r + 1 := by
    by_contra hnot
    have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h hd
    let := s.quasisimple
    let := simple_of_center_bot hz
    have he := SecondaryActionData.component_primeRank_eq_one_of_inner_power s D h
      Nat.prime_three (by decide) hd
      (by rw [hz, card_bot]; decide)
      ((by decide : Nat.Coprime 3 2).mul_right
        (Nat.prime_three.coprime_iff_not_dvd.mpr hnot)) (by
          intro a
          obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
          let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
            e.isSimpleGroup_congr.mp inferInstance
          have hh := J.odd_prime_unitary_power_inner hr hro hF hc (MulAut.congr e a)
          rw [← map_pow, ← MulAut.map_innerSubgroup_congr e] at hh
          obtain ⟨b, hb, he⟩ := hh
          exact ((MulAut.congr e).injective he) ▸ hb)
    omega
  have hh := Nat.mod_eq_zero_of_dvd hdiv
  omega
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
