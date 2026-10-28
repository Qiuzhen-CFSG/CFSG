module
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.GroupAction.ThirtyOneOnThirtyTwoIrreducible
public import Theory.GroupTheory.Fitting.Core

/-!
# A normal thirty-one subgroup in a solvable automorphism group

Let E be an elementary abelian group of order thirty-two. Any solvable
subgroup K of its automorphism group of order 9920 has a normal Sylow
thirty-one subgroup, of order thirty-one. The action is faithful because
K consists of actual automorphisms; no additional action or kernel assumption
is supplied.

A Sylow thirty-one subgroup has order thirty-one and acts irreducibly on E
by orbit counting. Thus K acts irreducibly as well. Its two-core has a
nonidentity fixed point by the characteristic-two fixed-point theorem.
Its five-core also has a nonidentity fixed point, since the fixed subgroup
has cardinal congruent to thirty-two modulo five. Normality makes both fixed
subgroups K-invariant, so irreducibility and faithful evaluation force both
cores to be trivial. Solvability makes the Fitting subgroup nontrivial.
Since the only primes dividing |K| are two, five, and thirty-one, its
prime-core decomposition leaves a nontrivial thirty-one core. That core
has the same order as a Sylow thirty-one subgroup and hence equals it.

This source-neutral Fitting argument supplies the solvable reduction in the
order-thirty-one branch of Parrott, "A Characterization of the Tits' Simple
Group", Canadian Journal of Mathematics 24 (1972), Lemma 2, printed p.673.
-/

public theorem normal_thirtyone_of_solvable_aut32_card9920
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (K : Subgroup (MulAut E))
    (hsolv : Group.IsSolvable K) (hK : Nat.card K = 9920) :
    ∃ P : Sylow 31 K, Nat.card P = 31 ∧ (P : Subgroup K).Normal := by
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Group.IsSolvable K := hsolv
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  let P : Sylow 31 K := default
  have hP : Nat.card P = 31 := by
    rw [Sylow.card_eq_multiplicity, hK]
    change 31 ^ Nat.factorization (2 ^ 6 * 5 * 31) 31 = 31
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, (show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 31 by decide).factorization]
  let A : Subgroup (MulAut E) := (P : Subgroup K).map K.subtype
  have hA : Nat.card A = 31 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hP
  have hAK : A ≤ K := Subgroup.map_subtype_le _
  have hirr : ∀ D : Subgroup E, (∀ a : K, ∀ x : E, x ∈ D → a • x ∈ D) →
      D = ⊥ ∨ D = ⊤ := by
    intro D hD
    apply irreducible_of_card_thirtyone hE A hA D
    intro a x hx
    exact hD ⟨a, hAK a.property⟩ x hx
  have htwo : pCore 2 K = ⊥ := irreducible_range_two_core_eq_bot K hirr
  have hfive : pCore 5 K = ⊥ := by
    let N : Subgroup K := pCore 5 K
    have hnonzero : FixedPoints.subgroup N E ≠ ⊥ := by
      intro hbot
      have hmod := (pCore_isPGroup (p := 5) (G := K)).card_modEq_card_fixedPoints E
      change Nat.ModEq 5 (Nat.card E) (Nat.card (FixedPoints.subgroup N E)) at hmod
      rw [hE, hbot, Subgroup.card_bot] at hmod
      norm_num [Nat.ModEq] at hmod
    have hinv := fixedPoints_isInvariant_of_normalizing_actor (V := E)
      (⊤ : Subgroup K) N (by rw [Subgroup.normalizer_eq_top])
    have hfix : FixedPoints.subgroup N E = ⊤ :=
      (hirr _ (fun a x hx => (hinv.invariant ⟨a, Subgroup.mem_top a⟩ x).mp hx)).resolve_left
        hnonzero
    apply bot_unique
    intro a ha
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have hx : x ∈ FixedPoints.subgroup N E := by rw [hfix]; trivial
    exact hx ⟨a, ha⟩
  have hthirtyone : pCore 31 K ≠ ⊥ := by
    intro hbot
    have hfit : fittingSubgroup K = ⊥ := by
      rw [fitting_eq_sup_pCore]
      apply iSup_eq_bot.mpr
      intro p
      have hp : p.val.val ∈ (9920 : ℕ).primeFactors := by
        simpa only [hK] using p.val.property
      have hprimes : (9920 : ℕ).primeFactors = {2, 5, 31} := by
        change (2 ^ 6 * 5 * 31 : ℕ).primeFactors = _
        rw [Nat.primeFactors_mul (by decide) (by decide),
          Nat.primeFactors_mul (by decide) (by decide),
          Nat.primeFactors_prime_pow (by decide) Nat.prime_two]
        norm_num [show Nat.Prime 5 by decide, show Nat.Prime 31 by decide]
      rw [hprimes] at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h
      · simpa only [h] using htwo
      · simpa only [h] using hfive
      · simpa only [h] using hbot
    have := (fitting_eq_bot_iff_card_eq_one_of_solvable K).mp hfit
    omega
  have hle : pCore 31 K ≤ P := pCore_isPGroup.le_sylow_of_normal P
  have hcard : Nat.card (pCore 31 K) = 31 := by
    have hdiv : Nat.card (pCore 31 K) ∣ 31 := by
      simpa only [hP] using Subgroup.card_dvd_of_le hle
    exact ((Nat.dvd_prime (by decide : Nat.Prime 31)).mp hdiv).resolve_left
      (fun h => hthirtyone (Subgroup.card_eq_one.mp h))
  have heq : pCore 31 K = (P : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hP, hcard])
  refine ⟨P, hP, ?_⟩
  rw [← heq]
  infer_instance
