module

public import Theory.Representation.InvolutiveWeights
public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.ExtendScalars
public import Theory.Representation.GeneralLinearNatural
public import Theory.GroupTheory.PGroup.NormalAbelian
public import Theory.Frattini.SubgroupIndexBound
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Frattini quotients of two-groups of degree at most four

A finite two-group acting faithfully in degree at most four over a field of
characteristic different from two has at most seven Frattini generators.
Choose a normal abelian self-centralizing subgroup. Over an algebraic closure,
the quotient acts faithfully on its at most four character weights, so the
subgroup has index at most eight. Its first omega subgroup has at most sixteen
elements, detected by at most four sign characters. The subgroup-index bound
for the Frattini quotient gives the required product 128.

The last theorem applies this to the literal natural representation of an
injective matrix group. This is the small-degree input for the Sylow restriction
argument in Aschbacher–Smith, *The Classification of Quasithin Groups*, 4.4.3,
printed p.622; its weight-permutation method is the one used in A.3.21(c),
printed pp.55–56.
-/

public section
open scoped IsMulCommutative
open scoped TensorProduct
open Subgroup

namespace Representation

variable {F A V : Type*} [Field F] [Group A] [Finite A]
  [IsElementaryAbelian 2 A] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Sign characters bound a faithfully represented elementary two-group. -/
theorem elementary_card_le_pow_finrank_of_involutive
    (rho : Representation F A V) (hrho : Function.Injective rho) (h2 : (2 : F) ≠ 0) :
    Nat.card A ≤ 2 ^ Module.finrank F V := by
  classical
  have hpow (a : A) : a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have horder : (Nat.card A : F) ≠ 0 := by
    rw [hk, Nat.cast_pow]
    exact pow_ne_zero _ h2
  obtain ⟨hfinite, hweights⟩ := rho.characterWeight_card_le horder
  let : Finite rho.CharacterWeight := hfinite
  let := Fintype.ofFinite rho.CharacterWeight
  let f : A → (rho.CharacterWeight → rootsOfUnity 2 F) := fun a chi =>
    ⟨chi.val a, by
      rw [mem_rootsOfUnity, ← map_pow, hpow, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply rho.eq_of_characterWeight_values_of_involutive hrho hpow h2 a b
    intro chi
    simpa [f] using congrArg Subtype.val (congrFun hab chi)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun] at hcard
  calc
    Nat.card A ≤ Nat.card (rootsOfUnity 2 F) ^ Nat.card rho.CharacterWeight := hcard
    _ ≤ 2 ^ Nat.card rho.CharacterWeight :=
      Nat.pow_le_pow_left (card_rootsOfUnity F 2) _
    _ ≤ 2 ^ Module.finrank F V :=
      pow_le_pow_right' (by decide) hweights

end Representation

namespace Representation

variable {F P V : Type*} [Field F] [Group P] [Finite P]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A faithful odd-characteristic representation of degree at most four
bounds the whole two-group Frattini quotient by 128. -/
theorem card_frattini_quotient_le_128_of_faithful_degree_four
    (hP : IsPGroup 2 P) (rho : Representation F P V)
    (hrho : Function.Injective rho) (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F V ≤ 4) :
    Nat.card (P ⧸ frattini P) ≤ 128 := by
  classical
  obtain ⟨A, hAn, hAc, hCA⟩ := exists_normal_abelian_selfCentralizing hP
  let : A.Normal := hAn
  let : IsMulCommutative A := hAc
  let E := AlgebraicClosure F
  let sigma := rho.extendScalars E
  have hsigma : Function.Injective sigma :=
    (extendScalars_faithful_iff E rho).mp hrho
  have h2E : (2 : E) ≠ 0 := by
    intro h
    apply h2
    apply (algebraMap F E).injective
    simpa only [map_ofNat, map_zero] using h
  have horderAE : (Nat.card A : E) ≠ 0 := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup A).exists_card_eq
    rw [hk, Nat.cast_pow]
    exact pow_ne_zero _ h2E
  have hdimE : Module.finrank E (E ⊗[F] V) ≤ 4 := by
    simpa only [Module.finrank_baseChange] using hdim
  obtain ⟨hfinite, hweights⟩ :=
    characterWeight_card_le (sigma.comp A.subtype) horderAE
  let W := CharacterWeight (sigma.comp A.subtype)
  let : Finite W := hfinite
  let := Fintype.ofFinite W
  let i : P →* Subgroup.normalizer (A : Set P) :=
    (MonoidHom.id P).codRestrict _ (fun g => by
      rw [A.normalizer_eq_top]
      trivial)
  let f : P →* Equiv.Perm W :=
    ((automizerWeightPerm sigma A).comp A.normalizerMonoidHom.rangeRestrict).comp i
  have hker : f.ker = A := by
    have h := normalizerWeightPerm_ker sigma A hsigma horderAE
    ext g
    change i g ∈ ((automizerWeightPerm sigma A).comp
      A.normalizerMonoidHom.rangeRestrict).ker ↔ g ∈ A
    rw [h]
    change g ∈ Subgroup.centralizer (A : Set P) ↔ g ∈ A
    exact ⟨fun h => hCA h, fun h => A.le_centralizer h⟩
  have hdiv : A.index ∣ (Nat.card W).factorial := by
    rw [← hker, Subgroup.index_ker]
    have hd := f.range.card_subgroup_dvd_card
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using hd
  have hdiv24 : A.index ∣ 24 :=
    hdiv.trans (Nat.factorial_dvd_factorial (hweights.trans hdimE))
  have hidx24 : A.index ≤ 24 := by
    exact Nat.le_of_dvd (by decide) hdiv24
  obtain ⟨n, hncard⟩ := hP.index A
  have hnlt : n < 5 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hncard] at hh'
    norm_num at hh'
    omega
  have hi8 : A.index ≤ 8 := by
    rw [hncard] at hdiv24 ⊢
    interval_cases n <;> norm_num at *
  let O := omega₁ A (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hO : Nat.card O ≤ 16 := by
    exact (elementary_card_le_pow_finrank_of_involutive
      ((rho.comp A.subtype).comp O.subtype)
      ((hrho.comp A.subtype_injective).comp O.subtype_injective) h2).trans
      (pow_le_pow_right' (by decide) hdim)
  calc
    Nat.card (P ⧸ frattini P) ≤ A.index * Nat.card O :=
      hP.card_frattini_quotient_le_index_mul_omega_one A
    _ ≤ 8 * 16 := Nat.mul_le_mul hi8 hO
    _ = 128 := by norm_num

end Representation


namespace Representation

/-- Apply the degree-four bound to the natural action of an injective matrix
representation, retaining the supplied matrix homomorphism. -/
theorem card_frattini_quotient_le_128_of_injective_generalLinear
    {F P : Type*} [Field F] [Group P] [Finite P] {n : ℕ}
    (hP : IsPGroup 2 P) (f : P →* GL (Fin n) F)
    (hf : Function.Injective f) (h2 : (2 : F) ≠ 0) (hn : n ≤ 4) :
    Nat.card (P ⧸ frattini P) ≤ 128 := by
  apply card_frattini_quotient_le_128_of_faithful_degree_four hP
    ((generalLinearNatural n).comp f) ((generalLinearNatural_injective n).comp hf) h2
  simpa only [Module.finrank_pi, Fintype.card_fin] using hn

end Representation
