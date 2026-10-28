module

public import Theory.GroupAction.SubgroupConjugation
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Disjoint actions of elementary planes

If an elementary p-plane normalizes a disjoint subgroup whose order is
divisible by p, orbit counting makes the fixed subgroup's order divisible
by p. Cauchy's theorem supplies a fixed element of order p. Its cyclic
subgroup and the plane form an elementary group of order p³, contradicting
an ambient p-rank bound of two. Faithful actions give the centralizer
consequence through the actual normalizer-to-automorphism homomorphism.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.27, printed p.26. The argument works at every prime and only needs
the ambient rank bound at that prime.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup

/-- An elementary plane normalized disjointly from a subgroup excludes p from
that subgroup's order when the ambient p-rank is at most two. -/
public theorem coprime_card_of_normalized_disjoint_plane
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hr : primeRank p G ≤ 2) (P H : Subgroup G)
    [IsElementaryAbelian p P] (hc : Nat.card P = p ^ 2)
    (hn : P ≤ normalizer (H : Set G)) (hd : Disjoint P H) :
    Nat.Coprime p (Nat.card H) := by
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hdiv
  let : MulDistribMulAction P H := conjMulDistribMulActionOfLeNormalizer P H hn
  let F := FixedPoints.subgroup P H
  have hmod := (IsElementaryAbelian.isPGroup p P).card_modEq_card_fixedPoints H
  have hFdiv : p ∣ Nat.card F :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hdiv.modEq_zero_nat)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hFdiv
  let x : G := ((y : F) : H)
  have hx : orderOf x = p := by simpa only [x, Subgroup.orderOf_coe] using hy
  have hxH : x ∈ H := (y : H).property
  have hxC : x ∈ centralizer (P : Set G) := by
    intro a ha
    have hh := congrArg Subtype.val (y.property (⟨a, ha⟩ : P))
    change a * x * a⁻¹ = x at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let Q := zpowers x
  have hQH : Q ≤ H := zpowers_le.mpr hxH
  have hQC : Q ≤ centralizer (P : Set G) := zpowers_le.mpr hxC
  let : IsElementaryAbelian p Q :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  let : IsElementaryAbelian p (P ⊔ Q : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hQC
  have hbound := (primeRank_le_iff_elementary_card_le G).mp hr
    (P ⊔ Q) inferInstance
  rw [card_sup_eq_mul_of_normalizes_of_disjoint P Q
    (hQC.trans (centralizer_le_normalizer _)) (hd.mono_right hQH),
    hc, Nat.card_zpowers, hx] at hbound
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos _
  have hprime := (Fact.out : p.Prime).one_lt
  nlinarith

/-- A faithful elementary plane action has a centralizer of order prime to p
in an ambient group of p-rank at most two. -/
public theorem coprime_card_centralizer_of_faithful_plane
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hr : primeRank p G ≤ 2) (P U : Subgroup G)
    [IsElementaryAbelian p P] (hc : Nat.card P = p ^ 2)
    (hn : P ≤ normalizer (U : Set G))
    (hfaith : Function.Injective (U.normalizerMonoidHom.comp (inclusion hn))) :
    Nat.Coprime p (Nat.card (centralizer (U : Set G))) := by
  apply coprime_card_of_normalized_disjoint_plane hr P _ hc
    (hn.trans (normalizer_le_normalizer_centralizer U))
  apply disjoint_def.mpr
  intro x hxP hxC
  have hk : (⟨x, hn hxP⟩ : normalizer (U : Set G)) ∈ U.normalizerMonoidHom.ker := by
    rwa [normalizerMonoidHom_ker]
  have he : U.normalizerMonoidHom.comp (inclusion hn) ⟨x, hxP⟩ = 1 := hk
  exact congrArg Subtype.val (hfaith (he.trans (map_one _).symm))

end Subgroup
