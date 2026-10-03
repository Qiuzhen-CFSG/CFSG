module
public import Theory.GroupTheory.Fitting.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Tactic

/-!
# Recognizing the faithful C5 semidirect C4 group from the odd core

Let G be finite and solvable, with trivial two-core, odd core of order five,
and group order divisible by four. Then G is isomorphic to a semidirect
product of the literal cyclic groups C5 and C4 with an injective action.
In particular, order twenty and faithfulness are conclusions of the given
core hypotheses, rather than additional assumptions.

The odd core is nilpotent. The prime-core join formula for the Fitting
subgroup places every odd prime core in it and kills the two-core term, so
it is the whole Fitting subgroup. Solvable Fitting self-centralization makes
the kernel of conjugation on this cyclic five-group exactly the odd core.
Its automorphism group has order four; four-divisibility then forces the
conjugation image and the odd-core index to have order four. Schur-Zassenhaus
provides an actual complement. Its conjugation action is faithful, and the
cyclic unit group of F5 makes the complement cyclic. Transport of the native
semidirect decomposition to the two prescribed cyclic groups retains that
faithfulness.

This source-neutral recognition supplies the true local quotient in
Stellmacher, Journal of Algebra 190 (1997), proof of (10.1), assertion (19),
printed p.64. The geometric caller supplies all four actual group hypotheses.
-/

open scoped IsMulCommutative
public theorem exists_faithful_c5_semidirect_c4_of_odd_core_card_five
    {G : Type*} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (h2 : pCore 2 G = ⊥)
    (h5 : Nat.card (pPrimeCore 2 G) = 5) (h4 : 4 ∣ Nat.card G) :
    ∃ φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)),
      Function.Injective φ ∧
        Nonempty (G ≃* SemidirectProduct (Multiplicative (ZMod 5))
          (Multiplicative (ZMod 4)) φ) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let O := pPrimeCore 2 G
  have hOcard : Nat.card O = 5 := h5
  let _ : IsCyclic O := isCyclic_of_prime_card hOcard
  have hO5 : IsPGroup 5 O := IsPGroup.of_card (n := 1) (by simpa using hOcard)
  have hfit : O = fittingSubgroup G := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance,hO5.isNilpotent⟩
    · rw [fitting_eq_sup_pCore]
      refine iSup_le fun prime => ?_
      by_cases heq : prime.val.val = 2
      · rw [heq,h2]
        exact bot_le
      · apply le_sSup
        refine ⟨inferInstance,?_⟩
        obtain ⟨exponent,hcard⟩ :=
          (pCore_isPGroup (p := prime.val.val) (G := G)).exists_card_eq
        rw [hcard]
        exact ((Nat.coprime_primes Nat.prime_two
          (Nat.prime_of_mem_primeFactors prime.val.property)).mpr (Ne.symm heq)).pow_right _
  have hcentral : Subgroup.centralizer (O : Set G) ≤ O := by
    rw [hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  let conj : G →* MulAut O := MulAut.conjNormal
  have hker : conj.ker = O := by
    apply le_antisymm
    · intro g hg
      apply hcentral
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      have hfix := congrArg (fun f : MulAut O => (f ⟨o,ho⟩ : G)) hg
      change g*o*g⁻¹=o at hfix
      calc
        o*g = (g*o*g⁻¹)*g := by rw [hfix]
        _ = g*o := by group
    · intro g hg
      rw [MonoidHom.mem_ker]
      ext o
      rw [MulAut.conjNormal_apply,MulAut.one_apply]
      have hcomm := congrArg (fun o : O => (o:G)) (mul_comm (⟨g,hg⟩ : O) o)
      change g*(o:G)=(o:G)*g at hcomm
      rw [hcomm]
      simp [mul_assoc]
  have hAutCard : Nat.card (MulAut O) = 4 := by
    rw [IsCyclic.card_mulAut,hOcard]
    decide
  have himageBound : Nat.card conj.range ≤ 4 :=
    hAutCard ▸ Subgroup.card_le_card_group conj.range
  have hGcard : Nat.card G = 5 * Nat.card conj.range := by
    have hh := conj.ker.card_mul_index
    rw [Subgroup.index_ker,hker,hOcard] at hh
    exact hh.symm
  have h4image : 4 ∣ Nat.card conj.range := by
    rw [hGcard] at h4
    exact (by decide : Nat.Coprime 4 5).dvd_of_dvd_mul_left h4
  have himageCard : Nat.card conj.range = 4 :=
    le_antisymm himageBound (Nat.le_of_dvd Nat.card_pos h4image)
  have hindex : O.index = 4 := by
    rw [←hker,Subgroup.index_ker,himageCard]
  obtain ⟨K,hcomp⟩ := Subgroup.exists_right_complement'_of_coprime
    (show Nat.Coprime (Nat.card O) O.index by rw [hOcard,hindex]; decide)
  have hKcard : Nat.card K = 4 := hcomp.symm.index_eq_card.symm.trans hindex
  let γ : K →* MulAut O :=
    O.normalizerMonoidHom.comp (Subgroup.inclusion (O.normalizer_eq_top ▸ le_top))
  have hγinj : Function.Injective γ := by
    apply (MonoidHom.ker_eq_bot_iff γ).mp
    apply bot_unique
    intro k hk
    have hkO : (k:G) ∈ O := by
      rw [←hker]
      exact hk
    exact Subtype.ext (Subgroup.disjoint_def.mp hcomp.disjoint hkO k.property)
  let eAut : MulAut O ≃* (ZMod 5)ˣ := by
    have hh := IsCyclic.mulAutMulEquiv O
    rw [hOcard] at hh
    exact hh
  let _ : IsCyclic (MulAut O) := isCyclic_of_injective eAut.toMonoidHom eAut.injective
  let _ : IsCyclic K := isCyclic_of_injective γ hγinj
  have hC5 : Nat.card (Multiplicative (ZMod 5)) = 5 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 5) ≃ ZMod 5)]
    norm_num
  have hC4 : Nat.card (Multiplicative (ZMod 4)) = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4) ≃ ZMod 4)]
    norm_num
  let eO : O ≃* Multiplicative (ZMod 5) :=
    mulEquivOfCyclicCardEq (hOcard.trans hC5.symm)
  let eK : K ≃* Multiplicative (ZMod 4) :=
    mulEquivOfCyclicCardEq (hKcard.trans hC4.symm)
  let φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)) :=
    MonoidHom.comp (MulAut.congr eO) (γ.comp eK.symm)
  refine ⟨φ,(MulAut.congr eO).injective.comp (hγinj.comp eK.symm.injective),?_⟩
  exact ⟨(SemidirectProduct.mulEquivSubgroup hcomp).symm.trans (SemidirectProduct.congr' eO eK)⟩
