module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.Automorphisms
public import Theory.GroupTheory.Fitting.AutomorphismPrimeSupport

/-!
# Solvable prime support from bounded odd cores

With trivial two-core, the nontrivial prime cores have odd prime at most
three or five. The small-rank automorphism calculation and Fitting
self-centralization then exclude every other prime from the whole group.
This applies directly to the literal two-core quotient of an overgroup.

Source: Aschbacher--Smith 14.6.14, first paragraph, printed p.1032.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
variable {J : Type*} [Group J] [Finite J]

private theorem odd_prime_le_small_prime {p q : ℕ}
    (hp : p = 3 ∨ p = 5) (hq : q.Prime) (ho : Odd q) (hle : q ≤ p) :
    q = 3 ∨ (p = 5 ∧ q = 5) := by
  rcases hp with rfl | rfl
  · interval_cases q <;> norm_num at *
  · interval_cases q <;> norm_num at *

/-- The odd-core bound controls the whole order of a solvable two-core-free group. -/
theorem solvable_prime_support_of_small_odd_cores
    (hs : Group.IsSolvable J) (h2 : pCore 2 J = ⊥)
    {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hbound : ∀ q : ℕ, q.Prime → Odd q → pCore q J ≠ ⊥ → q ≤ p)
    (hrank : ∀ q : ℕ, q.Prime → Odd q → primeRank q J ≤ 2)
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card J) :
    r = 2 ∨ r = 3 ∨ (p = 5 ∧ r = 5) := by
  by_contra hn
  have hr2 : r ≠ 2 := fun hh => hn (Or.inl hh)
  have hro : Odd r := Nat.odd_iff.mpr (hr.eq_two_or_odd.resolve_left hr2)
  have hcore : pCore r J = ⊥ := by
    by_contra hh
    exact hn (Or.inr (odd_prime_le_small_prime hp hr hro (hbound r hr hro hh)))
  apply not_dvd_card_of_solvable_core_automorphisms hs hr hcore ?_ hd
  intro q hq hdiv
  by_cases hzero : pCore q J = ⊥
  · rw [hzero] at hdiv
    let : Subsingleton (MulAut (⊥ : Subgroup J)) :=
      ⟨fun a b => MulEquiv.ext (fun x => Subsingleton.elim _ _)⟩
    have hc : Nat.card (MulAut (⊥ : Subgroup J)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
    exact hr.not_dvd_one (hc ▸ hdiv)
  have hq2 : q ≠ 2 := fun hh => hzero (hh.symm ▸ h2)
  have hqo : Odd q := Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hq2)
  have hsmall := odd_prime_le_small_prime hp hq hqo (hbound q hq hqo hzero)
  let : Fact q.Prime := ⟨hq⟩
  have ha := small_rank_odd_automorphism_primes
    (hsmall.imp id And.right) (pCore_isPGroup (p := q) (G := J))
    ((primeRank_subgroup_le q (pCore q J)).trans (hrank q hq hqo)) hr hdiv
  apply hn
  rcases ha with hh | hh | ⟨hq5,hr5⟩
  · exact Or.inl hh
  · exact Or.inr (Or.inl hh)
  · have hp5 : p = 5 := by rcases hsmall with h | h <;> omega
    exact Or.inr (Or.inr ⟨hp5,hr5⟩)
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
