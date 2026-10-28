module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source

/-!
# The sign restriction in the noncyclic Cartan case

If the odd prime subgroup B is noncyclic, both cyclic factors in A.3.15(3)
are nontrivial. Its prime therefore divides both q - δ and q - ε. Opposite
signs would force that prime to divide two. The same divisibilities exclude
q = 3 when the prime of B exceeds three.

Source: Aschbacher–Smith, proof of 1.3.4, printed pp. 510–511. Noncyclicity
is essential to this inference and is retained explicitly in these lemmas.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J]

/-- A trivial left factor would make the whole group cyclic. -/
theorem CyclicDecomposition.left_ne_bot {B K : Subgroup J} (h : CyclicDecomposition B K) (hn : ¬ IsCyclic B) :
    B ⊓ K ≠ ⊥ := by
  intro he
  apply hn
  rw [← h.generated, he, bot_sup_eq]
  exact h.right_cyclic

/-- A trivial centralizer factor would make the whole group cyclic. -/
theorem CyclicDecomposition.right_ne_bot {B K : Subgroup J} (h : CyclicDecomposition B K) (hn : ¬ IsCyclic B) :
    B ⊓ centralizer (K : Set J) ≠ ⊥ := by
  intro he
  apply hn
  rw [← h.generated, he, sup_bot_eq]
  exact h.left_cyclic

private theorem prime_dvd_card_of_le [Finite J] {p : ℕ} [Fact p.Prime] {B H : Subgroup J}
    (hB : IsPGroup p B) (hH : H ≤ B) (hn : H ≠ ⊥) : p ∣ Nat.card H := by
  have hP : IsPGroup p H := hB.of_injective (inclusion hH) (inclusion_injective hH)
  rcases hP.card_eq_or_dvd with h | h
  · exact False.elim (hn (Subgroup.card_eq_one.mp h))
  · exact h

private theorem no_dvd_both {p q : ℕ} (hp : 2 < p) (hq : 1 ≤ q)
    (hm : p ∣ q - 1) (hpq : p ∣ q + 1) : False := by
  have htwo : p ∣ 2 := by
    convert Nat.dvd_sub hpq hm using 1
    omega
  have := Nat.le_of_dvd (by decide : 0 < 2) htwo
  omega

/-- Noncyclicity forces the linear/unitary sign to match the Sylow torus sign. -/
theorem CaseThree.sign_eq [Finite J] {D B S K : Subgroup J} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] {δ ε : Sign}
    (h : CaseThree D B S K q δ ε) (hB : IsPGroup p B)
    (hp : 2 < p) (hn : ¬ IsCyclic B) : δ = ε := by
  have hl : p ∣ ε.torusOrder q :=
    (prime_dvd_card_of_le hB inf_le_left (h.toCyclicDecomposition.left_ne_bot hn)).trans h.sl2_dvd
  have hr : p ∣ δ.torusOrder q :=
    (prime_dvd_card_of_le hB inf_le_left (h.toCyclicDecomposition.right_ne_bot hn)).trans h.centralizer_dvd
  have hq := (Fact.out : q.Prime).one_lt.le
  cases δ <;> cases ε
  · rfl
  · exact False.elim (no_dvd_both hp hq hr hl)
  · exact False.elim (no_dvd_both hp hq hl hr)
  · rfl

/-- The small field q = 3 cannot contain these two nontrivial p-factors. -/
theorem CaseThree.characteristic_gt_three [Finite J] {D B S K : Subgroup J} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] {δ ε : Sign}
    (h : CaseThree D B S K q δ ε) (hB : IsPGroup p B)
    (hp : 3 < p) (hn : ¬ IsCyclic B) : 3 < q := by
  have hl : p ∣ ε.torusOrder q :=
    (prime_dvd_card_of_le hB inf_le_left (h.toCyclicDecomposition.left_ne_bot hn)).trans h.sl2_dvd
  have hq := (Fact.out : q.Prime).one_lt
  by_contra hsmall
  have hthree : q = 3 := by obtain ⟨k, hk⟩ := h.odd_characteristic; omega
  subst q
  cases ε
  · have hle := Nat.le_of_dvd (by decide : 0 < Sign.linear.torusOrder 3) hl
    change p ≤ 2 at hle
    omega
  · have hle := Nat.le_of_dvd (by decide : 0 < Sign.unitary.torusOrder 3) hl
    change p ≤ 4 at hle
    have hprime := (Fact.out : p.Prime)
    have he : p = 4 := by omega
    subst p
    norm_num at hprime

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
