module

public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.Tactic

/-!
# Reductions for odd automorphisms of small two-groups

A faithful cyclic order-nine action on a two-group of order at most 32
is impossible: outside the fixed subgroup of its order-three subgroup,
the action is free. None of the possible proper subgroup orders has
complement cardinality divisible by nine. Consequently an automorphism
subgroup whose cardinality divides nine is elementary abelian.

For the separate structural cardinal-bound problem, odd automorphism
subgroups act faithfully on the Frattini quotient, and noncommutativity
makes this quotient have at most half the original order. This module
does not assert the remaining automorphism cardinal bound.
-/

namespace SmallNonabelianTwoGroup

open scoped IsMulCommutative

private theorem nine_power_witness :
    ∀ element : Multiplicative (ZMod 9), element ≠ 1 →
      ∃ power : Fin 9, element ^ power.val = Multiplicative.ofAdd (3 : ZMod 9) := by
  decide

/-- A cyclic group of order nine cannot act faithfully on a two-group
of order at most thirty-two. -/
public theorem not_isCyclic_of_card_nine_of_faithful
    {Actor Core : Type*} [Group Actor] [Finite Actor] [Group Core] [Finite Core]
    [MulDistribMulAction Actor Core]
    (hactor : Nat.card Actor = 9) (htwo : IsPGroup 2 Core)
    (hbound : Nat.card Core ≤ 32)
    (hfaith : fixingSubgroup Actor (Set.univ : Set Core) = ⊥) :
    ¬ IsCyclic Actor := by
  classical
  intro hcyclic
  let : IsCyclic Actor := hcyclic
  let coordinates : Actor ≃* Multiplicative (ZMod 9) :=
    mulEquivOfCyclicCardEq (by simpa using hactor)
  let third : Actor := coordinates.symm (Multiplicative.ofAdd (3 : ZMod 9))
  have hthird : third ≠ 1 := by
    intro heq
    have hbad : Multiplicative.ofAdd (3 : ZMod 9) = 1 := by
      simpa [third] using congrArg coordinates heq
    exact (by decide : Multiplicative.ofAdd (3 : ZMod 9) ≠ 1) hbad
  let line := Subgroup.zpowers third
  have hline (element : Actor) (hne : element ≠ 1) :
      line ≤ Subgroup.zpowers element := by
    have hne' : coordinates element ≠ 1 := by simpa using hne
    obtain ⟨power, hpower⟩ := nine_power_witness (coordinates element) hne'
    rw [Subgroup.zpowers_le]
    have heq : element ^ power.val = third := by
      apply coordinates.injective
      simpa [third] using hpower
    rw [← heq]
    exact (Subgroup.zpowers element).pow_mem (Subgroup.mem_zpowers element) _
  let fixed : Subgroup Core := FixedPoints.subgroup line Core
  have hfixed : fixed ≠ ⊤ := by
    intro heq
    have hkernel : third ∈ fixingSubgroup Actor (Set.univ : Set Core) := by
      rw [mem_fixingSubgroup_iff]
      intro element _
      have hmem : element ∈ fixed := heq ▸ Subgroup.mem_top element
      exact (FixedPoints.mem_subgroup (M := line) (a := element)).mp hmem
        ⟨third, Subgroup.mem_zpowers third⟩
    rw [hfaith] at hkernel
    exact hthird hkernel
  let moved := {element : Core // element ∉ fixed}
  let : MulAction Actor moved :=
    { smul actor element := ⟨actor • (element : Core), by
        intro hmem
        apply element.property
        rw [FixedPoints.mem_subgroup] at hmem ⊢
        intro generator
        apply smul_left_cancel actor
        calc
          actor • ((generator : Actor) • (element : Core)) =
              (actor * (generator : Actor)) • (element : Core) := by rw [mul_smul]
          _ = ((generator : Actor) * actor) • (element : Core) := by rw [mul_comm]
          _ = (generator : Actor) • (actor • (element : Core)) := by rw [mul_smul]
          _ = actor • (element : Core) := hmem generator⟩
      one_smul element := Subtype.ext (one_smul Actor (element : Core))
      mul_smul first second element :=
        Subtype.ext (mul_smul first second (element : Core)) }
  have hstabilizer (element : moved) : MulAction.stabilizer Actor element = ⊥ := by
    apply eq_bot_iff.mpr
    intro actor hactorfix
    by_contra hne
    apply element.property
    rw [FixedPoints.mem_subgroup]
    intro generator
    exact smul_eq_self_of_mem_zpowers (hline actor hne generator.property)
      (congrArg Subtype.val hactorfix)
  have hmoved : 9 ∣ Nat.card moved := by
    rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstabilizer), Nat.card_prod,
      hactor]
    exact dvd_mul_left _ _
  let : Fintype Core := Fintype.ofFinite Core
  have hmovedcard : Nat.card moved = Nat.card Core - Nat.card fixed := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl (fun element : Core => element ∈ fixed)
  rw [hmovedcard] at hmoved
  obtain ⟨exponent, hcard⟩ := htwo.exists_card_eq
  have hexponent : exponent ≤ 5 := by
    by_contra hnot
    have hpower : 2 ^ 6 ≤ 2 ^ exponent :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hcard] at hpower
    change 64 ≤ Nat.card Core at hpower
    omega
  obtain ⟨dimension, hdimension, hfixedcard⟩ :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (hcard ▸ fixed.card_subgroup_dvd_card)
  have hstrict : dimension < exponent := by
    have hne : Nat.card fixed ≠ Nat.card Core := by
      intro heq
      exact hfixed (fixed.eq_top_of_card_eq heq)
    by_contra hnot
    have heq : dimension = exponent := by omega
    exact hne (by rw [hfixedcard, hcard, heq])
  rw [hcard, hfixedcard] at hmoved
  interval_cases exponent <;> interval_cases dimension <;> norm_num at hmoved

/-- Once its order divides nine, an automorphism subgroup of a two-group
of order at most thirty-two is elementary abelian. -/
public theorem elementaryAbelian_of_card_dvd_nine
    {Core : Type*} [Group Core] [Finite Core]
    (htwo : IsPGroup 2 Core) (hbound : Nat.card Core ≤ 32)
    (actor : Subgroup (MulAut Core)) (hcard : Nat.card actor ∣ 9) :
    IsElementaryAbelian 3 actor := by
  have hdiv : Nat.card actor ∣ 3 ^ 2 := by simpa using hcard
  obtain ⟨exponent, hexponent, hpower⟩ :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hdiv
  interval_cases exponent
  · have hsmall : Nat.card actor ∣ 3 := by rw [hpower]; norm_num
    let : IsCyclic actor := isCyclic_of_card_dvd_prime hsmall
    exact ⟨Group.exponent_dvd_nat_card.trans hsmall⟩
  · have hsmall : Nat.card actor ∣ 3 := by rw [hpower]; norm_num
    let : IsCyclic actor := isCyclic_of_card_dvd_prime hsmall
    exact ⟨Group.exponent_dvd_nat_card.trans hsmall⟩
  · let : IsMulCommutative actor :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq hpower
    have hfaith : fixingSubgroup actor (Set.univ : Set Core) = ⊥ := by
      apply eq_bot_iff.mpr
      intro element hfix
      apply Subtype.ext
      apply MulEquiv.ext
      intro point
      rw [mem_fixingSubgroup_iff] at hfix
      exact hfix point (Set.mem_univ point)
    have hnot := not_isCyclic_of_card_nine_of_faithful
      (by simpa using hpower) htwo hbound hfaith
    have hexp : Monoid.exponent actor = 3 :=
      (not_isCyclic_iff_exponent_eq_prime (by decide) hpower).mp hnot
    exact ⟨by rw [hexp]⟩

/-- An odd automorphism subgroup acts faithfully on the Frattini quotient. -/
public theorem odd_frattini_action_injective
    {Core : Type*} [Group Core] [Finite Core]
    (htwo : IsPGroup 2 Core) (actor : Subgroup (MulAut Core))
    (hodd : Odd (Nat.card actor)) :
    Function.Injective ((Subgroup.quotientAut (frattini Core)).comp
      actor.subtype) := by
  let quotientAction := Subgroup.quotientAut (frattini Core)
  obtain ⟨exponent, hcard⟩ :=
    (Subgroup.isPGroup_quotientAut_frattini_kernel htwo).exists_card_eq
  have hcoprime : Nat.Coprime (Nat.card actor) (Nat.card quotientAction.ker) := by
    rw [hcard]
    exact hodd.coprime_two_right.pow_right exponent
  have hdisjoint : Disjoint actor quotientAction.ker :=
    Subgroup.disjoint_of_coprime_natCard hcoprime
  rw [← MonoidHom.ker_eq_bot_iff]
  apply eq_bot_iff.mpr
  intro element hkernel
  apply Subtype.ext
  exact hdisjoint.le_bot ⟨element.property, hkernel⟩

/-- The Frattini quotient of a noncommutative two-group has at most half
the order of the original group. -/
public theorem frattini_quotient_card_le_half
    {Core : Type*} [Group Core] [Finite Core]
    (htwo : IsPGroup 2 Core) (hnoncomm : ¬ IsMulCommutative Core) :
    2 * Nat.card (Core ⧸ frattini Core) ≤ Nat.card Core := by
  let : Fact (IsPGroup 2 Core) := ⟨htwo⟩
  have hnontrivial : frattini Core ≠ ⊥ := by
    intro heq
    exact hnoncomm ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp heq).1
  have htwole : 2 ≤ Nat.card (frattini Core) := by
    have hlt := (frattini Core).one_lt_card_iff_ne_bot.mpr hnontrivial
    omega
  have hcount := (frattini Core).index_mul_card
  change Nat.card (Core ⧸ frattini Core) *
    Nat.card (frattini Core) = Nat.card Core at hcount
  nlinarith

end SmallNonabelianTwoGroup
