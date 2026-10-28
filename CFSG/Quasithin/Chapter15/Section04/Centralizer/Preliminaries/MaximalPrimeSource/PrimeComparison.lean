module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.PrimeExtraction
public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.ChapterA.Section01.RankActions.AutomorphismQuotient

/-!
# The noncircular maximal-prime comparison in 15.4.3

Maximality among lowercase ξ bounds every odd prime divisor of a solvable
overgroup of the ambient Sylow subgroup having nontrivial two-core. The
extraction theorem supplies either a lowercase ξ member of that index, or
an uppercase Ξ member whose quotient has order the square of that prime.
In the latter case the original 15.4.2(3) restriction gives three or five.
No use is made of 15.4.3(4), 15.4.4 or 15.4.5.

The action lemmas retain the prime-group kernel of A.1.25(2). A two-perfect
{2,p}-group cannot act nontrivially on a q-group of rank at most two when
q < p are odd primes: its linear image is a two-group, and its remaining
q-group image has order coprime to the actor.

Source: Aschbacher–Smith, combined manuscript, printed pp.1156–1157,
opening paragraph of the proof of 15.4.3; A.1.25(2), printed p.25.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource

variable {G : Type*} [Group G] [Finite G]

private theorem prime_eq_of_square_card {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup q A)
    (hc : Nat.card A = p ^ 2) : p = q := by
  let : Fact q.Prime := ⟨hq⟩
  have hd : p ∣ Nat.card A := by rw [hc, pow_two]; exact dvd_mul_right p p
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  exact Nat.prime_eq_prime_of_dvd_pow hp hq (hn ▸ hd)

/-- Maximality is only among lowercase ξ members. The uppercase alternative
uses precisely the quotient-prime consequence of earlier 15.4.2(3). -/
theorem odd_prime_le_maximal_xi (T : Sylow 2 G) (M X : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hM : M ∈ Chapter1.H G)
    (hs : Group.IsSolvable M) (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    (h42 : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G),
      IsPGroup 3 (Chapter1.XiQuotient Y) ∨ IsPGroup 5 (Chapter1.XiQuotient Y))
    (q : ℕ) (hq : q.Prime) (ho : Odd q) (hd : q ∣ Nat.card M)
    (hr : primeRank q M ≤ 2) : q ≤ (pCore 2 X).index := by
  obtain ⟨Y, _, hY | hY⟩ := PrimeExtraction.exists_member_of_solvable_overgroup
    T M hTM hM hs q hq ho hd hr
  · simpa only [hY.2] using hmax Y hY.1
  · rcases h42 Y hY.1 with h3 | h5
    · have he := prime_eq_of_square_card hq Nat.prime_three h3 hY.2
      omega
    · have he := prime_eq_of_square_card hq (by decide) h5 hY.2
      obtain ⟨k, hk⟩ := hX.2.2.2.2
      omega

/-- An actual maximal two-local supplies the rank bound from quasithinness
and the nontrivial two-core from its defining normalizer. -/
theorem maximal_twoLocal_odd_prime_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hsolv : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Group.IsSolvable M)
    (h42 : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G),
      IsPGroup 3 (Chapter1.XiQuotient Y) ∨ IsPGroup 5 (Chapter1.XiQuotient Y))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M)
    (q : ℕ) (hq : q.Prime) (ho : Odd q) (hd : q ∣ Nat.card M) :
    q ≤ (pCore 2 X).index :=
  odd_prime_le_maximal_xi T M X (le_sup_right.trans hXM)
    (Chapter1.mem_H_of_isTwoLocal hM.1) (hsolv M hM (le_sup_right.trans hXM))
    hX hp hmax h42 q hq ho hd ((hG.twoLocal_sqtk hM.1).stronglyQuasithin q hq ho)

/-- The defining prime index in lowercase ξ gives its literal prime support. -/
theorem xi_prime_support {T X : Subgroup G} (hX : X ∈ Xi T)
    (q : ℕ) (hq : q.Prime) (hd : q ∣ Nat.card X) :
    q = 2 ∨ q = (pCore 2 X).index := by
  rw [← (pCore 2 X).card_mul_index] at hd
  rcases hq.dvd_mul.mp hd with hc | hi
  · obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
    exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two (hn ▸ hc))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hX.2.2.2.1).mp hi)

/-- Excluding p from the target kills every homomorphism from a two-perfect
{2,p}-group. Its range is a two-group and also two-perfect. -/
theorem hom_eq_one_of_prime_not_dvd {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] {p : ℕ}
    (hA : IsPPerfect 2 A)
    (hs : ∀ q : ℕ, q.Prime → q ∣ Nat.card A → q = 2 ∨ q = p)
    (hb : ¬ p ∣ Nat.card B) (f : A →* B) : f = 1 := by
  have hr : IsPGroup 2 f.range := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
    intro q hq
    have hprime := Nat.prime_of_mem_primeFactors hq
    have hd := Nat.dvd_of_mem_primeFactors hq
    rcases hs q hprime (hd.trans (card_range_dvd f)) with rfl | rfl
    · simpa using Nat.prime_two
    · exact (hb (hd.trans f.range.card_subgroup_dvd_card)).elim
  apply MonoidHom.ker_eq_top_iff.mp
  exact hA f.ker inferInstance (hr.of_equiv (QuotientGroup.quotientKerEquivRange f).symm)

/-- A larger odd prime does not divide the order of GL₂ over the smaller
prime field. Oddness is needed to exclude p = q + 1. -/
theorem prime_not_dvd_card_GL₂ {p q : ℕ} (hp : p.Prime) [Fact q.Prime]
    (hop : Odd p) (hoq : Odd q) (hqp : q < p) :
    ¬ p ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) := by
  have hq : q.Prime := Fact.out
  have hqlo := hq.two_le
  have hplus : q + 1 < p := by
    obtain ⟨a, ha⟩ := hop
    obtain ⟨b, hb⟩ := hoq
    omega
  have hminus : ¬ p ∣ q - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hqnot : ¬ p ∣ q := Nat.not_dvd_of_pos_of_lt hq.pos hqp
  have hplusnot : ¬ p ∣ q + 1 := Nat.not_dvd_of_pos_of_lt (by omega) hplus
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [Nat.sub_mul, Nat.mul_add, Nat.one_mul, pow_two]
    omega
  rw [Matrix.card_GL_field]
  simp only [Fin.prod_univ_two, ZMod.card, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  rw [hsq, show q ^ 2 - q = q * (q - 1) by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]]
  simp only [hp.dvd_mul, hminus, hqnot, hplusnot, or_self, not_false_eq_true]

/-- A.1.25's q-group representation kernel is retained and then killed by
coprime prime support; no embedding of the whole automorphism group is used. -/
theorem small_rank_action_trivial {A P : Type*} [Group A] [Finite A]
    [Group P] [Finite P] {p q : ℕ} (hp : p.Prime) [Fact q.Prime]
    (hop : Odd p) (hoq : Odd q) (hqp : q < p)
    (hA : IsPPerfect 2 A)
    (hs : ∀ r : ℕ, r.Prime → r ∣ Nat.card A → r = 2 ∨ r = p)
    (hP : IsPGroup q P) (hr : primeRank q P ≤ 2)
    (a : A →* MulAut P) : a = 1 := by
  obtain ⟨f, hf⟩ := ChapterA.RankActions.smallRankAutomorphismRepresentation q hoq P hP hr
  have hlinear : f.comp a = 1 := hom_eq_one_of_prime_not_dvd hA hs
    (prime_not_dvd_card_GL₂ hp hop hoq hqp) (f.comp a)
  have hle : a.range ≤ f.ker := by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun hlinear x
  have har : IsPGroup q a.range := hf.to_le hle
  have hcard : Nat.card a.range = 1 := by
    apply har.card_eq_or_dvd.resolve_right
    intro hd
    rcases hs q Fact.out (hd.trans (card_range_dvd a)) with h2 | heq
    · rw [h2] at hoq
      norm_num at hoq
    · omega
  exact MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp hcard)

/-- The first centralization assertion in the proof of 15.4.3, on the
literal quotient M/O₂(M). All other-prime Fitting factors are centralized.
Quasithinness supplies their rank bounds through the two-group quotient. -/
theorem xi_centralizes_other_prime_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hsolv : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Group.IsSolvable M)
    (h42 : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G),
      IsPGroup 3 (Chapter1.XiQuotient Y) ∨ IsPGroup 5 (Chapter1.XiQuotient Y))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M)
    (q : ℕ) (hq : q.Prime) (ho : Odd q) (hne : q ≠ (pCore 2 X).index) :
    (X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M)) ≤
      centralizer (pCore q (M ⧸ pCore 2 M) : Set (M ⧸ pCore 2 M)) := by
  let : Fact q.Prime := ⟨hq⟩
  let Q := M ⧸ pCore 2 M
  let P := pCore q Q
  by_cases hz : P = ⊥
  · intro x _ y hy
    have hy1 : y = 1 := by
      change y ∈ P at hy
      rw [hz] at hy
      exact hy
    simp [hy1]
  have hqd : q ∣ Nat.card P := (pCore_isPGroup (p := q) (G := Q)).card_eq_or_dvd.resolve_left
    (fun hc => hz (Subgroup.card_eq_one.mp hc))
  have hqM : q ∣ Nat.card M :=
    (hqd.trans P.card_subgroup_dvd_card).trans (pCore 2 M).index_dvd_card
  have hqp : q < (pCore 2 X).index := lt_of_le_of_ne
    (maximal_twoLocal_odd_prime_le hG T hsolv h42 hX hp hmax hM hXM q hq ho hqM) hne
  have hr : primeRank q P ≤ 2 := (primeRank_subgroup_le q P).trans
    ((primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 M) pCore_isPGroup).trans
      ((hG.twoLocal_sqtk hM.1).stronglyQuasithin q hq ho))
  let f := (QuotientGroup.mk' (pCore 2 M)).comp (inclusion (le_sup_left.trans hXM))
  let a : X →* MulAut P := MulAut.conjNormal.comp f
  have ha : a = 1 := small_rank_action_trivial hX.2.2.2.1 hX.2.2.2.2 ho hqp
    hX.2.1 (xi_prime_support hX) pCore_isPGroup hr a
  rintro _ ⟨x, hx, rfl⟩
  apply mem_centralizer_iff.mpr
  intro v hv
  have he := congrArg (fun b : MulAut P => (b ⟨v, hv⟩ : Q))
    (DFunLike.congr_fun ha (⟨(x : G), hx⟩ : X))
  change QuotientGroup.mk' (pCore 2 M) x * v *
    (QuotientGroup.mk' (pCore 2 M) x)⁻¹ = v at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
