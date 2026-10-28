module
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Theory.GroupAction.Lemmas
public import Theory.Frattini.PGroup

/-!
# Five-actions on abelian groups of order thirty-two

An automorphism action of a group of order five on an abelian group V of
order thirty-two makes V elementary abelian when the common fixed subgroup
has order two. The supplied action is used throughout; faithfulness is not
an additional hypothesis.

Coprime action splits V into the fixed subgroup and the action commutator
subgroup C. The latter has order sixteen and trivial fixed subgroup. Orbit
counting on invariant subgroups of C shows that its characteristic Frattini
subgroup is trivial or full. The nongenerating property excludes the full
case, so the finite two-group C is elementary abelian. Each factor therefore
has exponent dividing two, and their product does as well.

This proves the elementary-abelian step in Parrott, "A Characterization of
the Tits' Simple Group", Canadian Journal of Mathematics 24 (1972), Lemma 1,
printed p.672, independently of the surrounding recognition hypotheses.
-/

open scoped IsMulCommutative Pointwise

namespace Theory.GroupAction

public theorem elementaryAbelian_of_card32_five_action
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hV : Nat.card V = 32)
    (hfixed : Nat.card (FixedPoints.subgroup A V) = 2) :
    IsElementaryAbelian 2 V := by
  let C : Subgroup V := commutatorAction A V
  let F : Subgroup V := FixedPoints.subgroup A V
  have hcompl : IsCompl F C :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun a b : V => mul_comm a b))
      (by rw [hA, hV]; decide) inferInstance
  have hcomp : F.IsComplement' C := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hcompl.disjoint
    apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨f, hf, c, hc, hfc⟩ := Subgroup.mem_sup.mp
      (show x ∈ F ⊔ C by rw [hcompl.sup_eq_top]; trivial)
    exact ⟨f, hf, c, hc, hfc⟩
  have hC : Nat.card C = 16 := by
    have hcount := hcomp.card_mul_card
    change Nat.card (FixedPoints.subgroup A V) * Nat.card C = Nat.card V at hcount
    rw [hfixed, hV] at hcount
    omega
  let : IsInvariant A V C := (commutatorAction_normal_and_invariant (A := A) (G := V)).2
  have hfixedC : FixedPoints.subgroup A C = ⊥ := by
    apply bot_unique
    intro c hc
    apply Subtype.ext
    have hmem : (c : V) ∈ F ⊓ C :=
      ⟨fun a => congrArg Subtype.val (hc a), c.property⟩
    simpa [hcompl.inf_eq_bot] using hmem
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 C) := ⟨IsPGroup.of_card (p := 2) (n := 4) (by simpa using hC)⟩
  let : IsInvariant A C (frattini C) := isInvariant_of_characteristic (frattini C)
  have hphi : frattini C = ⊥ := by
    rcases invariant_eq_bot_or_top_of_five_actor hA hC hfixedC (frattini C) with h | h
    · exact h
    · let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      have hbot : (⊥ : Subgroup C) = ⊤ := frattini_nongenerating (by simpa using h)
      exact (bot_ne_top hbot).elim
  let : IsElementaryAbelian 2 C := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
  }
  intro v
  obtain ⟨⟨f, c⟩, hfc⟩ := hcomp.surjective v
  change (f : V) * (c : V) = v at hfc
  have hf : (f : V) ^ 2 = 1 := by
    have hpow := pow_card_eq_one' (x := f)
    change f ^ Nat.card (FixedPoints.subgroup A V) = 1 at hpow
    rw [hfixed] at hpow
    exact congrArg Subtype.val hpow
  have hc : (c : V) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (A := C) (c : V) c.property
  rw [← hfc, mul_pow, hf, hc, one_mul]

end Theory.GroupAction
