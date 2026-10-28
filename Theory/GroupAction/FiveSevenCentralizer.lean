module
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.GroupAction.Lemmas
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Sylow

/-!
# A seven-free centralizer from a fixed-point-free five-action

Let E be any finite group of order 256 and A an automorphism subgroup of
order five fixing only the identity. The centralizer of A in Aut(E) has
order prime to seven. No linear structure or endomorphism-ring calculation
is needed.

Indeed, for an order-seven subgroup B in that centralizer, D=C_E(B) is
A-invariant. Its order divides 256, is congruent to one modulo five, and
is congruent to 256 modulo seven. Among the nine divisors of 256 only
256 satisfies both congruences. Thus B fixes all of E, a contradiction.

This is an elementary finite-action bound. Its consumer is the natural
chief-factor calculation for the covered G₂(4) residual in Aschbacher–Smith,
Lemma 16.5.13, printed p.1202: the actual Frattini section has order 256,
and an order-five actor is fixed-point-free on its natural chief factors.
The consumer must establish those facts and the literal image containment.
-/

@[expose] public section
open Subgroup

namespace Theory.GroupAction

/-- A fixed-point-free five-action on a group of order 256 has seven-free
centralizer in the actual automorphism group. -/
theorem seven_coprime_centralizer_of_fixed_free_five
    {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 256) (A : Subgroup (MulAut E)) (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A E = ⊥) :
    Nat.Coprime 7 (Nat.card (centralizer (A : Set (MulAut E)))) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr
  intro hseven
  let C := centralizer (A : Set (MulAut E))
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 7 hseven
  let b : MulAut E := c
  have hb : orderOf b = 7 :=
    (orderOf_injective C.subtype C.subtype_injective c).trans hc
  let B := zpowers b
  have hB : Nat.card B = 7 := (Nat.card_zpowers b).trans hb
  have hBA : B ≤ centralizer (A : Set (MulAut E)) := zpowers_le.mpr c.property
  have hAB : A ≤ centralizer (B : Set (MulAut E)) := le_centralizer_iff.mp hBA
  let D := FixedPoints.subgroup B E
  let : IsInvariant A E D := fixedPoints_isInvariant_of_normalizing_actor A B
    (hAB.trans (Subgroup.centralizer_le_normalizer _))
  have hcommon : Nat.card (FixedPoints.subgroup A D) = 1 := by
    rw [← card_map_of_injective D.subtype_injective,
      fixedPoints_subgroup_map_subtype_eq_inf, hfixed, inf_bot_eq, card_bot]
  have hpA : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hpB : IsPGroup 7 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hmod5 := hpA.card_modEq_card_fixedPoints D
  have hmod7 := hpB.card_modEq_card_fixedPoints E
  change Nat.card D % 5 = Nat.card (FixedPoints.subgroup A D) % 5 at hmod5
  change Nat.card E % 7 = Nat.card D % 7 at hmod7
  rw [hcommon] at hmod5
  rw [hE] at hmod7
  have hdiv : Nat.card D ∣ 256 := hE ▸ D.card_subgroup_dvd_card
  have hmem := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  have hdivs : (256 : ℕ).divisors = {1, 2, 4, 8, 16, 32, 64, 128, 256} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hD : Nat.card D = 256 := by omega
  have htop : D = ⊤ := D.eq_top_of_card_eq (hD.trans hE.symm)
  have heq : b = 1 := by
    apply MulEquiv.ext
    intro x
    have hx : x ∈ D := htop ▸ mem_top x
    exact hx ⟨b, mem_zpowers b⟩
  rw [heq, orderOf_one] at hb
  omega
end Theory.GroupAction
