module

public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.AbelianAllWeights
public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.ExtendScalars
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Binary actions on abelian odd-prime groups of rank at most two

A faithful elementary abelian two-group acting on a finite abelian odd-prime
`p`-group acts faithfully on the Frattini quotient.  That quotient has vector
space dimension at most two when the `p`-rank is at most two.  After extending
scalars to an algebraic closure, simultaneous character spaces embed the actor
in two copies of the roots of unity of order two, giving the sharp bound four.

The ambient theorem passes an arbitrary normalizing action to its actual image;
its kernel is the relative centralizer, so the same bound is the required
relative index bound.

This is the elementary action bound used after (*) in E.6.20 of
Aschbacher--Smith, *The Classification of Quasithin Groups*, printed p.253.
-/

open scoped TensorProduct
open scoped IsMulCommutative
open Subgroup

/-- A faithful elementary abelian two-group acting on a finite abelian odd
`p`-group of `p`-rank at most two has order at most four. -/
public theorem card_le_four_of_faithful_elementary_two_action
    {A P : Type*} [Group A] [Finite A] [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    [IsElementaryAbelian 2 A] [IsMulCommutative P]
    (hP : IsPGroup p P) (action : A →* MulAut P) (hfaith : Function.Injective action)
    (hrank : primeRank p P ≤ 2) : Nat.card A ≤ 4 := by
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P action
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    isElementaryAbelian_quotient_frattini (p := p)
  let hcop : Nat.Coprime (Nat.card A) p := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [hn]
    exact hp.coprime_two_left.pow_left n
  let qaction : MulDistribMulAction A (P ⧸ frattini P) :=
    quotientMulDistribMulAction (frattini P) (isInvariant_of_characteristic (frattini P))
  let : MulDistribMulAction A (P ⧸ frattini P) := qaction
  let qhom : A →* MulAut (P ⧸ frattini P) :=
    Subgroup.quotientAut (frattini P) |>.comp action
  have hqhom : Function.Injective qhom := by
    exact MonoidHom.injective_frattini_action_of_coprime
      hP action hfaith hcop
  have hqaction : Function.Injective (MulDistribMulAction.toMulAut A (P ⧸ frattini P)) := by
    intro a b hab
    apply hqhom
    ext x
    have hh := congrArg (fun z : MulAut (P ⧸ frattini P) => z x) hab
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) x
    rw [show qhom a = Subgroup.quotientAut (frattini P) (action a) by rfl,
      show qhom b = Subgroup.quotientAut (frattini P) (action b) by rfl,
      Subgroup.quotientAut_apply_mk, Subgroup.quotientAut_apply_mk]
    exact hh
  have hrankPtop : Group.rank (↥(⊤ : Subgroup P)) ≤ primeRank p P := by
    exact Subgroup.rank_le_primeRank p (⊤ : Subgroup P) (hP.to_subgroup (⊤ : Subgroup P))
  have hrankP : Group.rank P ≤ primeRank p P := by
    rw [← Group.rank_congr (Subgroup.topEquiv (G := P))]
    exact hrankPtop
  have hrankQ : Group.rank (P ⧸ frattini P) ≤ 2 := by
    rw [← Group.rank_eq_rank_quotient_frattini P]
    exact hrankP.trans hrank
  have hpowQ : ∀ x : P ⧸ frattini P, x ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (P ⧸ frattini P))
  have hcardQ : Nat.card (P ⧸ frattini P) ≤ p ^ 2 := by
    have hdvd := card_dvd_exponent_pow_rank' (P ⧸ frattini P) hpowQ
    exact (Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos
      (Group.rank (P ⧸ frattini P))) hdvd).trans
      (pow_le_pow_right' (Fact.out : p.Prime).one_lt.le hrankQ)
  have hdimQ : Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) ≤ 2 := by
    have hcard_eq : Nat.card (P ⧸ frattini P) =
        p ^ Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) := by
      calc
        Nat.card (P ⧸ frattini P) = Nat.card (Additive (P ⧸ frattini P)) :=
          Nat.card_congr Additive.ofMul
        _ = p ^ Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) := by
          simpa only [Nat.card_zmod] using
            (Module.natCard_eq_pow_finrank (K := ZMod p)
              (V := Additive (P ⧸ frattini P)))
    have hcardQ' : p ^ Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) ≤ p ^ 2 := by
      rw [← hcard_eq]
      exact hcardQ
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcardQ'
  let rho₀ : Representation (ZMod p) A (Additive (P ⧸ frattini P)) :=
    Representation.ofElementaryAbelianAction
  have hrho₀ : Function.Injective rho₀ := by
    intro a b hab
    apply hqaction
    ext x
    have hh := congrArg (fun z : Module.End (ZMod p) (Additive (P ⧸ frattini P)) =>
      z x) hab
    exact hh
  let E := AlgebraicClosure (ZMod p)
  let sigma : Representation E A (E ⊗[ZMod p] (Additive (P ⧸ frattini P))) :=
    rho₀.extendScalars E
  have hsigma : Function.Injective sigma :=
    (Representation.extendScalars_faithful_iff E rho₀).mp hrho₀
  have horder : (Nat.card A : E) ≠ 0 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [hn, Nat.cast_pow]
    have htwo : (2 : E) ≠ 0 := by
      intro h
      have hdiv : p ∣ 2 := CharP.cast_eq_zero_iff E p 2 |>.mp h
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
      · exact (Fact.out : Nat.Prime p).ne_one h1
      · apply hp.not_two_dvd_nat
        simp [h2]
    exact pow_ne_zero n htwo
  obtain ⟨hfinite, hweights⟩ := sigma.characterWeight_card_le horder
  let := hfinite
  have hdimSigma : Module.finrank E (E ⊗[ZMod p] (Additive (P ⧸ frattini P))) ≤ 2 := by
    simpa only [Module.finrank_baseChange] using hdimQ
  have hweights2 : Nat.card sigma.CharacterWeight ≤ 2 := hweights.trans hdimSigma
  let evaluate : A → (sigma.CharacterWeight → rootsOfUnity 2 E) := fun a chi =>
    ⟨chi.val a, by
      rw [mem_rootsOfUnity, ← map_pow]
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a, map_one]⟩
  have hevaluate : Function.Injective evaluate := by
    intro a b hab
    apply Representation.eq_of_characterWeight_values sigma hsigma horder a b
    intro chi
    exact Units.ext (congrArg (fun z : rootsOfUnity 2 E => (z.val : E)) (congrFun hab chi))
  calc
    Nat.card A ≤ Nat.card (sigma.CharacterWeight → rootsOfUnity 2 E) :=
      Nat.card_le_card_of_injective evaluate hevaluate
    _ = Nat.card (rootsOfUnity 2 E) ^ Nat.card sigma.CharacterWeight := Nat.card_fun
    _ ≤ 2 ^ Nat.card sigma.CharacterWeight :=
      Nat.pow_le_pow_left (card_rootsOfUnity E 2) _
    _ ≤ 2 ^ 2 := pow_le_pow_right' (by decide) hweights2
    _ = 4 := by norm_num

/-- A two-subgroup normalizing an abelian odd-prime subgroup of prime rank at
most two has relative centralizer index at most four.  The action is reduced
through its actual image, so no faithfulness of the original action is needed. -/
public theorem relIndex_le_four_of_elementaryAbelian_two_normalizing_abelian_odd
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (V P : Subgroup G) (hV : IsElementaryAbelian 2 V)
    (hPcomm : IsMulCommutative P) (hP : IsPGroup p P)
    (hnorm : V ≤ Subgroup.normalizer (P : Set G))
    (hrank : primeRank p P ≤ 2) :
    (V ⊓ Subgroup.centralizer (P : Set G)).relIndex V ≤ 4 := by
  let : IsElementaryAbelian 2 V := hV
  let : IsMulCommutative P := hPcomm
  let f : V →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hbound : Nat.card f.range ≤ 4 := by
    exact card_le_four_of_faithful_elementary_two_action hp hP f.range.subtype
      f.range.subtype_injective hrank
  have hk : f.ker = (V ⊓ Subgroup.centralizer (P : Set G)).subgroupOf V := by
    ext x
    constructor
    · intro hx
      have hx' : (Subgroup.inclusion hnorm x) ∈ P.normalizerMonoidHom.ker := hx
      rw [Subgroup.normalizerMonoidHom_ker] at hx'
      exact ⟨x.property, hx'⟩
    · intro hx
      have hx' : (Subgroup.inclusion hnorm x) ∈ P.normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        exact hx.2
      exact hx'
  change ((V ⊓ Subgroup.centralizer (P : Set G)).subgroupOf V).index ≤ 4
  rw [← hk, Subgroup.index_ker]
  exact hbound
