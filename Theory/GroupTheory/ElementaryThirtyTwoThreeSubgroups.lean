module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Three-subgroups on an elementary abelian group of order thirty-two

The order of GL(5,2) has three-part nine. Hence every three-subgroup of
the automorphism group has order dividing nine and is elementary abelian:
the cyclic-nine case is excluded by the existing faithful-action argument.
An order-three subgroup has either two or eight fixed elements, by counting
orbits modulo three and using the possible subgroup orders. An order-nine
subgroup fixes exactly two elements: otherwise its faithful action on the
commutator summand would embed it in GL(2,2), of order six. Coprime splitting
then gives a commutator summand of order sixteen.

These are the initial structural reductions for the three-core exclusion
in Parrott, "A Characterization of the Tits' Simple Group" (1972), printed
p.673, properties (1) and (4), used on p.677 after Lemma 5. The normalizer
bounds and the three-core exclusion are separate from these reductions.
-/

open Subgroup
open scoped IsMulCommutative

/-- The order of the automorphism group of an elementary abelian group of order 32. -/
public theorem card_mulAut_of_elementary_thirtytwo
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) : Nat.card (MulAut E) = 9999360 := by
  have h := SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 5 hE
  norm_num [Fin.prod_univ_succ] at h
  exact h

/-- Every three-subgroup of GL(5,2) has order dividing nine. -/
public theorem card_three_subgroup_dvd_nine_of_elementary_thirtytwo
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (hA : IsPGroup 3 A) :
    Nat.card A ∣ 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdiv : 3 ^ n ∣ 9999360 := by
    rw [← hn, ← card_mulAut_of_elementary_thirtytwo hE]
    exact A.card_subgroup_dvd_card
  have hnle : n ≤ 2 := by
    by_contra! hh
    have hbad : 27 ∣ 9999360 := (pow_dvd_pow 3 hh).trans hdiv
    norm_num at hbad
  rw [hn]
  exact pow_dvd_pow 3 hnle

/-- Three-subgroups of GL(5,2) are elementary abelian. -/
public theorem elementaryAbelian_three_subgroup_of_elementary_thirtytwo
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (hA : IsPGroup 3 A) :
    IsElementaryAbelian 3 A := by
  exact SmallNonabelianTwoGroup.elementaryAbelian_of_card_dvd_nine
    (IsElementaryAbelian.isPGroup 2 E) (by omega) A
    (card_three_subgroup_dvd_nine_of_elementary_thirtytwo hE A hA)

/-- A nontrivial three-subgroup on an elementary thirty-two has two or eight fixed points. -/
public theorem fixed_card_two_or_eight_of_elementary_thirtytwo_three_subgroup
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (hp : IsPGroup 3 A)
    (hne : A ≠ ⊥) :
    Nat.card (FixedPoints.subgroup A E) = 2 ∨
      Nat.card (FixedPoints.subgroup A E) = 8 := by
  let F := FixedPoints.subgroup A E
  have hmod := hp.card_modEq_card_fixedPoints E
  change Nat.card E % 3 = Nat.card F % 3 at hmod
  rw [hE] at hmod
  have hdiv : Nat.card F ∣ 2 ^ 5 := by
    change Nat.card F ∣ 32
    rw [← hE]
    exact F.card_subgroup_dvd_card
  have hproper : Nat.card F ≠ 32 := by
    intro hh
    have htop : F = ⊤ := F.eq_top_of_card_eq (hh.trans hE.symm)
    have hbot : A = ⊥ := by
      apply eq_bot_iff.mpr
      intro a ha
      apply mem_bot.mpr
      apply MulEquiv.ext
      intro x
      have hx : x ∈ F := htop ▸ mem_top x
      exact hx ⟨a, ha⟩
    exact hne hbot
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  change Nat.card F = 2 ∨ Nat.card F = 8
  interval_cases n <;> norm_num only [Nat.reducePow] at hcard <;> omega

/-- An order-three subgroup on an elementary thirty-two has two or eight fixed points. -/
public theorem fixed_card_two_or_eight_of_elementary_thirtytwo_three
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (hA : Nat.card A = 3) :
    Nat.card (FixedPoints.subgroup A E) = 2 ∨
      Nat.card (FixedPoints.subgroup A E) = 8 := by
  apply fixed_card_two_or_eight_of_elementary_thirtytwo_three_subgroup hE A
    (IsPGroup.of_card (n := 1) (by simpa using hA))
  intro hbot
  rw [hbot, card_bot] at hA
  omega

/-- An order-nine subgroup fixes exactly a line and has commutator space of order sixteen. -/
public theorem fixed_and_commutator_card_of_elementary_thirtytwo_nine
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (hA : Nat.card A = 9) :
    Nat.card (FixedPoints.subgroup A E) = 2 ∧ Nat.card (commutatorAction A E) = 16 := by
  let F := FixedPoints.subgroup A E
  let U := commutatorAction A E
  let : IsInvariant A E U := commutatorAction_isInvariant
  have hcompl : IsCompl F U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun x y : E => mul_comm x y))
      (by rw [hA, hE]; decide) inferInstance
  have hcount : Nat.card F * Nat.card U = 32 := by
    have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes F U
      (by rw [normalizer_eq_top]; exact le_top)
    simpa only [hcompl.inf_eq_bot, hcompl.sup_eq_top, card_bot, card_top, one_mul, hE]
      using h
  have hfaith : Function.Injective (MulDistribMulAction.toMulAut A U) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨f, hf, u, hu, rfl⟩ := Subgroup.mem_sup.mp
      (show x ∈ F ⊔ U by rw [hcompl.sup_eq_top]; trivial)
    have hufix : a • u = u := by
      have hh := congrArg (fun b : MulAut U => b ⟨u, hu⟩) ha
      exact congrArg Subtype.val hh
    change a • (f * u) = f * u
    rw [smul_mul', hf a, hufix]
  have hdiv := Subgroup.card_dvd_of_injective (MulDistribMulAction.toMulAut A U) hfaith
  have hp : IsPGroup 3 A := IsPGroup.of_card (n := 2) hA
  have hne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hA
    omega
  change Nat.card F = 2 ∧ Nat.card U = 16
  rcases fixed_card_two_or_eight_of_elementary_thirtytwo_three_subgroup hE A hp hne
    with htwo | height
  · change Nat.card F = 2 at htwo
    exact ⟨htwo, by rw [htwo] at hcount; omega⟩
  · change Nat.card F = 8 at height
    have hU : Nat.card U = 4 := by rw [height] at hcount; omega
    let : IsElementaryAbelian 2 U :=
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := by
          rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
          intro u
          apply Subtype.ext
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 E) (u : E) }
    have hAut := SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow U 2 hU
    norm_num [Fin.prod_univ_succ] at hAut
    rw [hA, hAut] at hdiv
    norm_num at hdiv
