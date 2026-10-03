module

public import Glauberman.SuzukiCharacterization.CentralizerReduction
public import Glauberman.ZStar.CharacterwiseSupport
public import Theory.Character.ModularBlock.NormalComplementValues
public import Theory.GroupTheory.NormalizedCoprimeCoset

/-!
# Principal-block values on normalized odd cosets

The group-theoretic transport conjugates `xy` by an element of the odd
subgroup to `xv`, where `v` has odd order and commutes with `x`. The
centralizer of nonidentity `x ∈ P` has a normal two-complement. Thus the
local character identity at `xv` gives equation (4.8).

The local section theorem in `NormalComplementValues` supplies this identity
for arbitrary two-elements. Applying it after the coprime conjugacy transport
proves the full coset identity for every nonidentity `x ∈ P`. The involution
specialization and the transport with an explicit local identity remain
available separately.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 3.8, p. 88, and equation (4.8), p. 90. The source is saved in
`refs/original/n-group-global/odd-core-rank-two-source/`.
-/

open Subgroup ModularBlock.PrincipalBlockConstruction

namespace Glauberman.SuzukiCharacterization

private theorem mem_oddCore_of_normal_two_complement
    {K : Type*} [Group K] [Finite K]
    (hc : HasNormalPComplement 2 K) (v : K)
    (hv : Nat.Coprime 2 (orderOf v)) : v ∈ pPrimeCore 2 K := by
  obtain ⟨N, hN, hcop, hquot⟩ := hc
  let := hN
  let q := QuotientGroup.mk' N
  have hqv : q v = 1 := by
    obtain ⟨k, hk⟩ := hquot.exists_orderOf_eq_pow (q v)
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (hv.pow_left k)
      (hk ▸ dvd_refl _) (orderOf_map_dvd q v)
  exact (show N ≤ pPrimeCore 2 K from le_sSup ⟨hN, hcop⟩)
    ((QuotientGroup.eq_one_iff (N := N) _).mp hqv)

/-- The local value identity for involutions with a normal two-complement
in their centralizer. The odd factor lies in the local odd core. -/
public theorem principal_value_mul_eq_of_involution
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) {i : d.I} (hi : i ∈ d.block)
    (u v : G) (hu : orderOf u = 2)
    (hc : HasNormalPComplement 2 (centralizer ({u} : Set G)))
    (huv : Commute u v) (hv : Nat.Coprime 2 (orderOf v)) :
    d.chi i (ConjClasses.mk (u * v)) = d.chi i (ConjClasses.mk u) := by
  have huI : BenderSuzuki.PFAppendixIII.IsInvolution u := by
    refine ⟨?_, ?_⟩
    · intro he
      simp [he] at hu
    · rw [← hu, pow_orderOf_eq_one]
  let vC : centralizer ({u} : Set G) :=
    ⟨v, mem_centralizer_singleton_iff.mpr huv.symm.eq⟩
  have hvC : vC ∈ pPrimeCore 2 (centralizer ({u} : Set G)) :=
    mem_oddCore_of_normal_two_complement hc vC
      (by simpa only [vC, Subgroup.orderOf_mk] using hv)
  exact ZStar.LocalBlockSection.section_invariance_of_canonicalLocalPrincipalBlockCoreSupport
    d (ZStar.CharacterwiseSupport.canonicalLocalPrincipalBlockCoreSupport d i hi u huI)
    ⟨vC, hvC, rfl⟩

/-- Equation (4.8) for involutions, using the established local section theorem. -/
public theorem Hypotheses.principal_coset_values_of_involution
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) {i : d.I} (hi : i ∈ d.block)
    (H : Subgroup G) (hodd : Nat.Coprime 2 (Nat.card H))
    (hnorm : (P : Subgroup G) ≤ normalizer (H : Set G))
    (x : P) (hx : orderOf x = 2) (y : H) :
    d.chi i (ConjClasses.mk ((x : G) * y)) = d.chi i (ConjClasses.mk (x : G)) := by
  obtain ⟨a, v, hxv, he⟩ :=
    P.exists_conj_mul_commuting_of_normalized_coprime H hodd hnorm x y
  have hclass : ConjClasses.mk ((x : G) * y) = ConjClasses.mk ((x : G) * v) :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨(a : G), he⟩)
  rw [hclass]
  have hxG : orderOf (x : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hx
  exact principal_value_mul_eq_of_involution d hi x v hxG
    (h.involution_complement x x.property hxG) hxv
    (hodd.of_dvd_right (H.orderOf_dvd_natCard v.property))

/-- The final transport for equation (4.8), with the general local
principal-block value identity left explicit. Nonidentity is required only
to obtain the normal two-complement in the element centralizer. -/
public theorem Hypotheses.principal_coset_values_of_local_values
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G)
    (hlocal : ∀ i ∈ d.block, ∀ u v : G,
      (∃ k : ℕ, u ^ (2 ^ k) = 1) → u ≠ 1 →
      HasNormalPComplement 2 (centralizer ({u} : Set G)) →
      Commute u v → Nat.Coprime 2 (orderOf v) →
      d.chi i (ConjClasses.mk (u * v)) = d.chi i (ConjClasses.mk u))
    {i : d.I} (hi : i ∈ d.block)
    (H : Subgroup G) (hodd : Nat.Coprime 2 (Nat.card H))
    (hnorm : (P : Subgroup G) ≤ normalizer (H : Set G))
    (x : P) (hx : x ≠ 1) (y : H) :
    d.chi i (ConjClasses.mk ((x : G) * y)) = d.chi i (ConjClasses.mk (x : G)) := by
  obtain ⟨a, v, hxv, he⟩ :=
    P.exists_conj_mul_commuting_of_normalized_coprime H hodd hnorm x y
  have hclass : ConjClasses.mk ((x : G) * y) = ConjClasses.mk ((x : G) * v) :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨(a : G), he⟩)
  rw [hclass]
  have hxG : (x : G) ≠ 1 := fun he => hx (Subtype.ext he)
  have hxpow : ∃ k : ℕ, (x : G) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' x
    exact ⟨k, congrArg Subtype.val hk⟩
  exact hlocal i hi x v hxpow hxG
    (h.centralizer_hasNormalPComplement P x x.property hxG) hxv
    (hodd.of_dvd_right (H.orderOf_dvd_natCard v.property))

/-- Glauberman's equation (4.8): a principal-block character is constant on
the coset `xH` when `H` has odd order and is normalized by `P`, and `x ∈ P`
is nonidentity. -/
public theorem Hypotheses.principal_coset_values
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) {i : d.I} (hi : i ∈ d.block)
    (H : Subgroup G) (hodd : Nat.Coprime 2 (Nat.card H))
    (hnorm : (P : Subgroup G) ≤ normalizer (H : Set G))
    (x : P) (hx : x ≠ 1) (y : H) :
    d.chi i (ConjClasses.mk ((x : G) * y)) = d.chi i (ConjClasses.mk (x : G)) := by
  apply h.principal_coset_values_of_local_values P d _ hi H hodd hnorm x hx y
  intro j hj u v hu _ hc huv hv
  obtain ⟨N, hN, hcop, hquot⟩ := hc
  let := hN
  exact ModularBlock.NormalComplementValues.principal_value_mul_eq_of_normal_two_complement
    d u v hu N hcop hquot huv hv hj

end Glauberman.SuzukiCharacterization
