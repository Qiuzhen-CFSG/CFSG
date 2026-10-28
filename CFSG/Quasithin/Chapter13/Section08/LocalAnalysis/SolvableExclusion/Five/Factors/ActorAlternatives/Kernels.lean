module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor.DiagonalComplement
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic

/-!
# The involution kernels on normalized five-factors

A nontrivial elementary abelian two-group acts faithfully by conjugation on
one or two cyclic groups of order five. Each restriction has at most two
values, since an involution centralizes or inverts a prime-order group.
If the actor has more than two elements, there must be two factors. The
kernel on the second factor is nontrivial and acts faithfully on the first,
so has order two. The diagonal-complement construction then supplies the
other involution and the complementary product of order four.

Normalization and joint faithfulness are explicit hypotheses of this algebraic
step. No displacement or offender conclusion is assumed or asserted here;
those and factor normalization remain separate steps in the source argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 / PDF p.968, the five-primary actor alternatives.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives
variable {K : Type*} [Group K] [Finite K]

private theorem faithful_prime_card_le_two (E Q : Subgroup K)
    [IsElementaryAbelian 2 E] (hQ : (Nat.card Q).Prime)
    (hn : E ≤ normalizer (Q : Set K))
    (hf : E ⊓ centralizer (Q : Set K) = ⊥) : Nat.card E ≤ 2 := by
  classical
  let r : E →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hn)
  have hker (x : E) : r x = 1 ↔ (x : K) ∈ centralizer (Q : Set K) := by
    constructor
    · intro h q hq
      have he := congrArg Subtype.val (congrArg (fun f : MulAut Q => f ⟨q, hq⟩) h)
      change (x : K) * q * (x : K)⁻¹ = q at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro h
      ext q
      change (x : K) * (q : K) * (x : K)⁻¹ = (q : K)
      rw [← h q q.property, mul_inv_cancel_right]
  have hinv (x : E) (hx : r x ≠ 1) :
      ∀ q ∈ Q, (x : K) * q * (x : K)⁻¹ = q⁻¹ := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one Q hQ x
      (elemPow_eq_one_of_isElementaryAbelian (x : K) x.property) (hn x.property) with hc | hi
    · exact (hx ((hker x).mpr fun q hq => (hc q hq).symm)).elim
    · exact hi
  have hr : Function.Injective r := by
    apply r.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hm : (x : K) ∈ E ⊓ centralizer (Q : Set K) := ⟨x.property, (hker x).mp hx⟩
    simpa only [hf, mem_bot, coe_one] using hm
  let b : E → Bool := fun x => decide (r x = 1)
  have hb : Function.Injective b := by
    intro x y he
    apply hr
    have he' : r x = 1 ↔ r y = 1 := decide_eq_decide.mp he
    by_cases hx : r x = 1
    · exact hx.trans (he'.mp hx).symm
    · have hy : r y ≠ 1 := fun hy => hx (he'.mpr hy)
      ext q
      exact (hinv x hx q q.property).trans (hinv y hy q q.property).symm
  simpa using Nat.card_le_card_of_injective b hb

omit [Finite K] in
private theorem joint_kernel {s : ℕ} (Q : Fin s → Subgroup K)
    (E D : Subgroup K) (hD : D ≤ E)
    (hf : E ⊓ centralizer ((⨆ i, Q i : Subgroup K) : Set K) = ⊥)
    (hc : ∀ i, D ≤ centralizer (Q i : Set K)) : D = ⊥ := by
  apply bot_unique
  apply le_trans (le_inf hD ?_) hf.le
  exact le_centralizer_iff.mpr (iSup_le fun i => le_centralizer_iff.mp (hc i))

/-- Faithful elementary two-actors on one or two normalized five-factors have
order two, or split into the two complementary involution kernels. The order-two
branch records movement of some factor; the action-ratio argument must still
exclude movement of both factors. -/
public theorem normalized_actor_alternative {s : ℕ} (hspos : 0 < s) (hsle : s ≤ 2)
    (Q : Fin s → Subgroup K) (hQ : ∀ i, Nat.card (Q i) = 5)
    (E : Subgroup K) [IsElementaryAbelian 2 E] (hne : E ≠ ⊥)
    (hn : ∀ i, E ≤ normalizer (Q i : Set K))
    (hf : E ⊓ centralizer ((⨆ i, Q i : Subgroup K) : Set K) = ⊥) :
    (Nat.card E = 2 ∧ ∃ i, ⁅E, Q i⁆ ≠ ⊥) ∨
      (s = 2 ∧ Nat.card E = 4 ∧ ∃ (i : Fin s) (A B : Subgroup K),
        i.val ≠ 0 ∧ A ≤ E ∧ B ≤ E ∧ Nat.card A = 2 ∧ Nat.card B = 2 ∧
        E = A ⊔ B ∧ Disjoint A B ∧ ⁅A, B⁆ = ⊥ ∧
        ⁅A, Q ⟨0, hspos⟩⁆ ≠ ⊥ ∧ ⁅A, Q i⁆ = ⊥ ∧
        ⁅B, Q ⟨0, hspos⟩⁆ = ⊥ ∧ ⁅B, Q i⁆ ≠ ⊥) := by
  classical
  have hp (i : Fin s) : (Nat.card (Q i)).Prime := by rw [hQ]; decide
  by_cases hsmall : Nat.card E ≤ 2
  · left
    have hgt := E.one_lt_card_iff_ne_bot.mpr hne
    refine ⟨by omega, ?_⟩
    by_contra hm
    push Not at hm
    exact hne (joint_kernel Q E E le_rfl hf
      (fun i => commutator_eq_bot_iff_le_centralizer.mp (hm i)))
  · have hlarge : 2 < Nat.card E := by omega
    have hs : s = 2 := by
      by_contra hs
      have hsone : s = 1 := by omega
      have hfaith : E ⊓ centralizer (Q ⟨0, hspos⟩ : Set K) = ⊥ := by
        apply joint_kernel Q E _ inf_le_left hf
        intro i
        have hi : i = ⟨0, hspos⟩ := Fin.ext (by have := i.isLt; omega)
        rw [hi]
        exact inf_le_right
      have := faithful_prime_card_le_two E _ (hp ⟨0, hspos⟩) (hn _) hfaith
      omega
    let z : Fin s := ⟨0, hspos⟩
    let i : Fin s := ⟨1, by omega⟩
    let A := E ⊓ centralizer (Q i : Set K)
    have hAE : A ≤ E := inf_le_left
    let : IsElementaryAbelian 2 A := {
      is_comm := ⟨fun x y => Subtype.ext
        (congrArg (fun e : E => (e : K))
          (mul_comm (⟨x, hAE x.property⟩ : E) ⟨y, hAE y.property⟩))⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : K) (hAE x.property)) }
    have hAne : A ≠ ⊥ := by
      intro he
      have := faithful_prime_card_le_two E (Q i) (hp i) (hn i) he
      omega
    have hAf : A ⊓ centralizer (Q z : Set K) = ⊥ := by
      apply joint_kernel Q E _ (inf_le_left.trans hAE) hf
      intro j
      by_cases hj : j.val = 0
      · have hjz : j = z := Fin.ext hj
        rw [hjz]
        exact inf_le_right
      · have hji : j = i := Fin.ext (by have := j.isLt; dsimp [i]; omega)
        rw [hji]
        exact inf_le_left.trans inf_le_right
    have hAc : Nat.card A = 2 := by
      have hle := faithful_prime_card_le_two A (Q z) (hp z) (hAE.trans (hn z)) hAf
      have hgt := A.one_lt_card_iff_ne_bot.mpr hAne
      omega
    have hAm : ⁅A, Q z⁆ ≠ ⊥ := by
      intro he
      have hle := commutator_eq_bot_iff_le_centralizer.mp he
      exact hAne (by simpa only [inf_eq_left.mpr hle] using hAf)
    have hrest (j : Fin s) (hj : j.val ≠ 0) : ⁅A, Q j⁆ = ⊥ := by
      have hji : j = i := Fin.ext (by have := j.isLt; dsimp [i]; omega)
      rw [hji]
      exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
    obtain ⟨_, j, B, hj, hBE, hBc, hgen, hd, hc, hB0, hBj⟩ :=
      CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor.DiagonalComplement.exists_complement
        hspos hsle Q hQ E A hAE hAc hlarge hn hf hAm hrest
    have hEc : Nat.card E = 4 := by
      have hnBA : B ≤ normalizer (A : Set K) :=
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
          (centralizer_le_normalizer _)
      rw [hgen, card_sup_eq_mul_of_normalizes_of_disjoint A B hnBA hd, hAc, hBc]
    exact Or.inr ⟨hs, hEc, j, A, B, hj, hAE, hBE, hAc, hBc, hgen, hd, hc,
      hAm, hrest j hj, hB0, hBj⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives
