module
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.GroupTheory.Fitting.Centralizer
public import Mathlib.RingTheory.IntegralDomain

/-!
# Elementary two-subgroups in solvable two-five automorphism groups

Let E be an elementary abelian two-group of order sixteen. If a solvable
subgroup K of Aut(E) has order 2^n * 5, each elementary abelian two-subgroup
of K has order at most two. All actions are the canonical evaluation actions
of the actual automorphism subgroups; irreducibility and normality are
conclusions of the argument.

A Sylow five-subgroup has order five, so its faithful action on E has
trivial fixed subgroup and is irreducible by the existing orbit-counting
bounds. Consequently K acts irreducibly, which forces its two-core to be
trivial. Its 5-prime core has order dividing 2^n and is therefore also
trivial. The Fitting subgroup is the five-core, whose nontriviality and
order bound identify it with the Sylow five-subgroup P. Solvable Fitting
self-centralization gives C_K(P) contained in P.

An elementary two-subgroup A thus has trivial intersection with the kernel
of conjugation on P. It embeds into Aut(P), a cyclic group identified with
the units of the field with five elements. Since A is cyclic and has
exponent dividing two, its order divides two.

This supplies the local-solvability replacement for the GL(4,2) subgroup
exclusion at the end of Parrott, *A characterization of the Tits' simple
group* (1972), Lemma 3, printed p.675. It does not require a classification
of the subgroups of GL(4,2).
-/

open Subgroup
open scoped IsMulCommutative

/-- Elementary two-subgroups of these solvable automorphism groups have order at most two. -/
public theorem card_elementary_two_le_two_of_solvable_aut16_two_five
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 16) (K : Subgroup (MulAut E))
    (hsolv : Group.IsSolvable K) {n : ℕ} (hK : Nat.card K = 2 ^ n * 5)
    (A : Subgroup K) [IsElementaryAbelian 2 A] : Nat.card A ≤ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Group.IsSolvable K := hsolv
  let P : Sylow 5 K := default
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hK,
      Nat.factorization_mul (by positivity) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, (show Nat.Prime 5 by decide).factorization]
  have hfixne : FixedPoints.subgroup P E ≠ ⊤ := by
    intro htop
    have hbot : (P : Subgroup K) = ⊥ := by
      apply bot_unique
      intro a ha
      apply mem_bot.mpr
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      have hx : x ∈ FixedPoints.subgroup P E := by rw [htop]; trivial
      exact hx ⟨a, ha⟩
    have hone : Nat.card P = 1 := by
      rw [hbot, Subgroup.card_bot]
    omega
  have hfixed := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen hP hE hfixne
  have hirr : ∀ D : Subgroup E, (∀ a : K, ∀ x : E, x ∈ D → a • x ∈ D) →
      D = ⊥ ∨ D = ⊤ := by
    intro D hD
    let : IsInvariant P E D := ⟨by
      intro a x
      constructor
      · exact hD (a : K) x
      · intro hx
        change (a : K) • x ∈ D at hx
        simpa only [inv_smul_smul] using hD (a : K)⁻¹ ((a : K) • x) hx⟩
    exact invariant_eq_bot_or_top_of_five_actor hP hE hfixed D
  have htwo : pCore 2 K = ⊥ := irreducible_range_two_core_eq_bot K hirr
  have hfivePrime : pPrimeCore 5 K = ⊥ := by
    let Q : Subgroup K := pPrimeCore 5 K
    have hcop : Nat.Coprime (Nat.card Q) 5 :=
      (pPrimeCore_coprime_card (p := 5) (G := K)).symm
    have hdiv : Nat.card Q ∣ 2 ^ n * 5 := by
      simpa only [hK] using Q.card_subgroup_dvd_card
    have hQtwo : IsPGroup 2 Q := IsPGroup.of_card_dvd_pow
      (hcop.dvd_of_dvd_mul_right hdiv)
    have hle : Q ≤ pCore 2 K := le_sSup ⟨inferInstance, hQtwo⟩
    exact bot_unique (htwo ▸ hle)
  have hfit : fittingSubgroup K = pCore 5 K := Fitting_eq_pcore K 5 hfivePrime
  have hfive : pCore 5 K ≠ ⊥ := by
    intro hbot
    have hcardone := (fitting_eq_bot_iff_card_eq_one_of_solvable K).mp (hfit.trans hbot)
    have hdiv : 5 ∣ Nat.card K := by rw [hK]; exact dvd_mul_left 5 (2 ^ n)
    rw [hcardone] at hdiv
    norm_num at hdiv
  have hleP : pCore 5 K ≤ P := pCore_isPGroup.le_sylow_of_normal P
  have hcorecard : Nat.card (pCore 5 K) = 5 := by
    have hdiv : Nat.card (pCore 5 K) ∣ 5 := by
      simpa only [hP] using card_dvd_of_le hleP
    exact ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdiv).resolve_left
      (fun hh => hfive (Subgroup.card_eq_one.mp hh))
  have hcoreP : pCore 5 K = (P : Subgroup K) :=
    eq_of_le_of_card_ge hleP (by rw [hP, hcorecard])
  let : (P : Subgroup K).Normal := by rw [← hcoreP]; infer_instance
  have hfitP : fittingSubgroup K = (P : Subgroup K) := hfit.trans hcoreP
  have hcentral : centralizer ((P : Subgroup K) : Set K) ≤ (P : Subgroup K) := by
    simpa only [hfitP] using centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  have hnorm : A ≤ normalizer ((P : Subgroup K) : Set K) := by rw [Subgroup.normalizer_eq_top]; exact le_top
  let γ : A →* MulAut P :=
    (P : Subgroup K).normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hdis : Disjoint A (P : Subgroup K) :=
    IsPGroup.disjoint_of_ne 2 5 (by decide) _ _
      (IsElementaryAbelian.isPGroup 2 A) P.isPGroup'
  have hinj : Function.Injective γ := by
    apply (MonoidHom.ker_eq_bot_iff γ).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    have haker : Subgroup.inclusion hnorm a ∈ (P : Subgroup K).normalizerMonoidHom.ker := ha
    rw [Subgroup.normalizerMonoidHom_ker] at haker
    have haP : (a : K) ∈ (P : Subgroup K) := hcentral haker
    exact Subtype.ext (Subgroup.disjoint_def.mp hdis a.property haP)
  let : IsCyclic P := isCyclic_of_prime_card hP
  let eAut : MulAut P ≃* (ZMod 5)ˣ := by
    have hh := IsCyclic.mulAutMulEquiv P
    rw [hP] at hh
    exact hh
  let : IsCyclic (MulAut P) := isCyclic_of_injective eAut.toMonoidHom eAut.injective
  let : IsCyclic A := isCyclic_of_injective γ hinj
  have hdiv : Nat.card A ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 A
  exact Nat.le_of_dvd (by decide) hdiv
