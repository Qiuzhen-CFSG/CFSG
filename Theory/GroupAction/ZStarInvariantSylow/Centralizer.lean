module

public import Theory.GroupAction.CoprimeQuotientFixedConjugacy
public import Theory.GroupAction.ZStarInvariantSylow.Extension

/-!
# Centralizer Sylows for involutions central modulo the odd core

An invariant Sylow p-subgroup contains a Sylow p-subgroup of the fixed
subgroup when a two-group acts trivially modulo an odd normal subgroup and
p is odd. Extend a Sylow of the fixed subgroup to an invariant Sylow of the
whole group, then use a fixed conjugator to move it into the chosen Sylow.
Conjugation by that fixed element preserves the original fixed subgroup.

The external-involution version identifies the fixed subgroup of the literal
conjugation action on W with W intersect C_G(t), retaining the original
subtype maps. Neither W nor its two-point overgroup is assumed odd.

Source: GLS, Volume 4, Chapter 2, Proposition 3.7(b), printed p.30.
The source application is SectionThree.Local.Sylow in the ZD development.
-/

open Subgroup
open BenderSuzuki.PFAppendixIII

namespace ZStarInvariantSylow

/-- An invariant Sylow contains a Sylow of the fixed subgroup when every
displacement lies in an odd normal subgroup. -/
public theorem exists_fixed_sylow_le_of_odd_normal_displacement
    {A K : Type*} [Group A] [Group K] [Finite K] [MulDistribMulAction A K]
    (hA : IsPGroup 2 A) (N : Subgroup K) [N.Normal]
    (hN : Odd (Nat.card N))
    (hdisp : ∀ (a : A) (k : K), (a • k) * k⁻¹ ∈ N)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (Q : Sylow p K) (hQI : IsInvariant A K (Q : Subgroup K)) :
    ∃ R : Sylow p (fixedPointSubgroup A K),
      (R : Subgroup (fixedPointSubgroup A K)).map
        (fixedPointSubgroup A K).subtype ≤ Q := by
  classical
  let C := fixedPointSubgroup A K
  let R : Sylow p C := default
  let S : Subgroup K := (R : Subgroup C).map C.subtype
  have hSC : S ≤ C := by simpa [S] using map_le_range C.subtype (R : Subgroup C)
  have hSI : IsInvariant A K S := by
    refine ⟨fun a k => ⟨fun hk => ?_, fun hk => ?_⟩⟩
    · rw [(hSC hk) a]
      exact hk
    · have he := (hSC hk) a⁻¹
      rw [inv_smul_smul] at he
      exact he.symm ▸ hk
  obtain ⟨P, hSP, hPI⟩ := exists_invariant_sylow_of_odd_normal_displacement
    hA N hN hdisp hpodd S (R.isPGroup'.map C.subtype) hSI
  obtain ⟨k, hk, he⟩ := Theory.GroupAction.exists_fixed_sylow_conjugator_of_normal_displacement
    hA N hN.not_two_dvd_nat hdisp P Q hPI hQI
  let c : C := ⟨k, hk⟩
  let R' := R.mapSurjective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).surjective
  refine ⟨R', ?_⟩
  rintro x ⟨xc, hxc, rfl⟩
  change xc ∈ (R : Subgroup C).map (MulAut.conj c).toMonoidHom at hxc
  obtain ⟨y, hy, rfl⟩ := hxc
  rw [← he]
  exact ⟨(y : K), hSP ⟨y, hy, rfl⟩, rfl⟩

/-- The centralizer-Sylow assertion for an external involution acting
trivially modulo the relative odd core. -/
public theorem exists_centralizer_sylow_le
    {G : Type*} [Group G] [Finite G] {t : G} (ht : IsInvolution t)
    {W : Subgroup G} (htW : t ∈ normalizer (W : Set G))
    (hcore : ⁅W, zpowers t⁆ ≤ (pPrimeCore 2 W).map W.subtype)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (Q : Sylow p W)
    (htQ : t ∈ normalizer (((Q : Subgroup W).map W.subtype) : Set G)) :
    ∃ R : Sylow p (W ⊓ centralizer ({t} : Set G) : Subgroup G),
      (R : Subgroup (W ⊓ centralizer ({t} : Set G) : Subgroup G)).map
        (W ⊓ centralizer ({t} : Set G)).subtype ≤
          (Q : Subgroup W).map W.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  let A : Subgroup G := zpowers t
  have hAW : A ≤ normalizer (W : Set G) := zpowers_le.mpr htW
  let : Normalizes A W := ⟨hAW⟩
  have hA : IsPGroup 2 A := by
    apply IsPGroup.of_card (n := 1)
    change Nat.card (zpowers t) = 2 ^ 1
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ht.sq_eq_one ht.ne_one
  let QG : Subgroup G := (Q : Subgroup W).map W.subtype
  have hAQ : A ≤ normalizer (QG : Set G) := zpowers_le.mpr htQ
  have hmem (x : W) : (x : G) ∈ QG ↔ x ∈ (Q : Subgroup W) := by
    constructor
    · rintro ⟨y, hy, he⟩
      exact W.subtype_injective he ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hQI : IsInvariant A W (Q : Subgroup W) := by
    refine ⟨fun a x => ?_⟩
    rw [← hmem x, ← hmem (a • x)]
    exact mem_normalizer_iff.mp (hAQ a.property) (x : G)
  obtain ⟨R, hRQ⟩ := exists_fixed_sylow_le_of_odd_normal_displacement
    hA (pPrimeCore 2 W) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    (displacement_mem_of_commutator_le hcore) hpodd Q hQI
  let C : Subgroup G := W ⊓ centralizer ({t} : Set G)
  let F := fixedPointSubgroup A W
  let e : F ≃* C := {
    toFun x := ⟨((x : W) : G), (x : W).property, by
      apply mem_centralizer_singleton_iff.mpr
      have hx := congrArg W.subtype (x.property (⟨t, mem_zpowers t⟩ : A))
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩
    invFun x := ⟨⟨(x : G), x.property.1⟩, by
      intro a
      apply Subtype.ext
      change (a : G) * (x : G) * (a : G)⁻¹ = (x : G)
      have hx : (x : G) ∈ centralizer (A : Set G) := by
        simpa only [A, zpowers_eq_closure, centralizer_closure] using
          (show (x : G) ∈ centralizer ({t} : Set G) from x.property.2)
      rw [mem_centralizer_iff.mp hx a a.property, mul_inv_cancel_right]⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨R', ?_⟩
  rintro x ⟨xc, hxc, rfl⟩
  change xc ∈ (R : Subgroup F).map e.toMonoidHom at hxc
  obtain ⟨y, hy, rfl⟩ := hxc
  exact ⟨(y : W), hRQ ⟨y, hy, rfl⟩, rfl⟩

end ZStarInvariantSylow
