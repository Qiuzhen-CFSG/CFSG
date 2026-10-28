module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Distinct local symmetric-four conjugation images

Let U be an order-eight subgroup of a finite group with Sylow two-subgroups
of order 128. Two order-192 subgroups K and L normalize U, intersect in order
64, and have supplied S₄ quotient models with kernel U. If their intersections
with C(U) are U and C(U) is a two-group, their actual conjugation images are
distinct S₄ subgroups of the range of the normalizer action on U.

The first isomorphism theorem identifies the restricted conjugation ranges
with the supplied models by equality of kernels. If the ranges coincide,
their full preimage in N(U) contains both K and L. Its order is 24 times a
power of two, since the conjugation kernel is C(U). Lagrange's theorem and
the odd index of an ambient Sylow two-subgroup bound this order by 384.
Consequently [D : L] is at most two, whereas [K : K ∩ L] is three, contrary
to monotonicity of relative index. No ambient normality of K or L, or
self-centralization of U, is required.

This independent finite-group argument supplies the counting step used in
Stellmacher (9.1)(c), Journal of Algebra 190 (1997), p.48 / PDF p.38,
`refs/files/stellmacher-n-group.pdf`. It has no campaign imports.
-/

private theorem restricted_conjugation_model
    {H : Type*} [Group H] (U K : Subgroup H)
    (hKN : K ≤ Subgroup.normalizer (U : Set H))
    (hKC : K ⊓ Subgroup.centralizer (U : Set H) = U)
    (hmodel : ∃ f : K →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = U.subgroupOf K) :
    Nonempty ((U.normalizerMonoidHom.rangeRestrict.comp
      (Subgroup.inclusion hKN)).range ≃* Equiv.Perm (Fin 4)) := by
  let action := U.normalizerMonoidHom.rangeRestrict.comp (Subgroup.inclusion hKN)
  have hker : action.ker = U.subgroupOf K := by
    rw [show action = U.normalizerMonoidHom.rangeRestrict.comp
      (Subgroup.inclusion hKN) from rfl, ← MonoidHom.comap_ker,
      MonoidHom.ker_rangeRestrict, Subgroup.normalizerMonoidHom_ker]
    ext element
    change (element : H) ∈ Subgroup.centralizer (U : Set H) ↔ (element : H) ∈ U
    constructor
    · intro hc
      have hm : (element : H) ∈ K ⊓ Subgroup.centralizer (U : Set H) :=
        ⟨element.property, hc⟩
      rwa [hKC] at hm
    · intro hu
      have hm : (element : H) ∈ K ⊓ Subgroup.centralizer (U : Set H) := hKC.symm ▸ hu
      exact hm.2
  obtain ⟨model, hsurj, hmodelker⟩ := hmodel
  exact ⟨(QuotientGroup.quotientKerEquivRange action).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hker.trans hmodelker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective model hsurj))⟩

private theorem card_bound_from_sylow
    {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
    (S0 : Sylow 2 H) (hS : Nat.card S0 = 128)
    (embedding : D →* H) (hinj : Function.Injective embedding)
    (exponent : ℕ) (hcard : Nat.card D = 24 * 2 ^ exponent) :
    Nat.card D ≤ 384 := by
  have hdiv := Subgroup.card_dvd_of_injective embedding hinj
  have hambient := S0.toSubgroup.card_mul_index
  rw [hS] at hambient
  have hpower : 2 ^ (exponent + 3) ∣ Nat.card D := by
    rw [hcard, pow_add]
    exact ⟨3, by ring⟩
  have hdiv' : 2 ^ (exponent + 3) ∣ 128 * S0.index :=
    hambient.symm ▸ hpower.trans hdiv
  have hcop : Nat.Coprime (2 ^ (exponent + 3)) S0.index :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr S0.not_dvd_index).pow_left _
  have hle := Nat.le_of_dvd (by norm_num : 0 < 128)
    (hcop.dvd_of_dvd_mul_right hdiv')
  rw [pow_add] at hle
  norm_num at hle
  rw [hcard]
  omega

/-- The two local S₄ quotients give distinct subgroups of the actual normalizer
conjugation range when the ambient Sylow order is 128. -/
public theorem two_symmetric_four_conjugation_images_of_sylow_bound
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (hS : Nat.card S0 = 128)
    (U K L : Subgroup H) (_hU : Nat.card U = 8)
    (hK : Nat.card K = 192) (hL : Nat.card L = 192)
    (hKL : Nat.card ↥(K ⊓ L) = 64)
    (_hUK : U ≤ K) (_hUL : U ≤ L)
    (hKN : K ≤ Subgroup.normalizer (U : Set H))
    (hLN : L ≤ Subgroup.normalizer (U : Set H))
    (hC : IsPGroup 2 (Subgroup.centralizer (U : Set H)))
    (hKC : K ⊓ Subgroup.centralizer (U : Set H) = U)
    (hLC : L ⊓ Subgroup.centralizer (U : Set H) = U)
    (hmodelK : ∃ f : K →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = U.subgroupOf K)
    (hmodelL : ∃ f : L →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = U.subgroupOf L) :
    ∃ X Y : Subgroup U.normalizerMonoidHom.range,
      X ≠ Y ∧ Nonempty (X ≃* Equiv.Perm (Fin 4)) ∧
        Nonempty (Y ≃* Equiv.Perm (Fin 4)) := by
  classical
  let normalizer := Subgroup.normalizer (U : Set H)
  let action := U.normalizerMonoidHom.rangeRestrict
  let leftAction := action.comp (Subgroup.inclusion hKN)
  let rightAction := action.comp (Subgroup.inclusion hLN)
  obtain ⟨leftModel⟩ := restricted_conjugation_model U K hKN hKC hmodelK
  obtain ⟨rightModel⟩ := restricted_conjugation_model U L hLN hLC hmodelL
  refine ⟨leftAction.range, rightAction.range, ?_, ⟨leftModel⟩, ⟨rightModel⟩⟩
  intro heq
  let preimage := leftAction.range.comap action
  let overgroup := preimage.map normalizer.subtype
  have hKover : K ≤ overgroup := by
    intro element helement
    refine ⟨⟨element, hKN helement⟩, ?_, rfl⟩
    exact ⟨⟨element, helement⟩, rfl⟩
  have hLover : L ≤ overgroup := by
    intro element helement
    refine ⟨⟨element, hLN helement⟩, ?_, rfl⟩
    change action ⟨element, hLN helement⟩ ∈ leftAction.range
    rw [heq]
    exact ⟨⟨element, helement⟩, rfl⟩
  have hkernel : action.ker =
      (Subgroup.centralizer (U : Set H)).subgroupOf normalizer := by
    exact (MonoidHom.ker_rangeRestrict _).trans U.normalizerMonoidHom_ker
  have hkernelP : IsPGroup 2 action.ker := by
    rw [hkernel]
    exact hC.comap_of_injective normalizer.subtype Subtype.coe_injective
  obtain ⟨exponent, hexponent⟩ := hkernelP.exists_card_eq
  have hkerPre : action.ker ≤ preimage := by
    intro element helement
    change action element ∈ leftAction.range
    rw [MonoidHom.mem_ker.mp helement]
    exact leftAction.range.one_mem
  have hmap : preimage.map action = leftAction.range := by
    apply Subgroup.map_comap_eq_self
    rw [action.range_eq_top_of_surjective U.normalizerMonoidHom.rangeRestrict_surjective]
    exact le_top
  have hcardImage : Nat.card leftAction.range = 24 := by
    rw [Nat.card_congr leftModel.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hcardPre : Nat.card preimage = 24 * 2 ^ exponent := by
    have hcount := (action.ker.subgroupOf preimage).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerPre).toEquiv] at hcount
    change Nat.card action.ker * action.ker.relIndex preimage = Nat.card preimage at hcount
    rw [Subgroup.relIndex_ker, hmap, hcardImage, hexponent] at hcount
    omega
  have hpreBound : Nat.card preimage ≤ 384 :=
    card_bound_from_sylow S0 hS (normalizer.subtype.comp preimage.subtype)
      (Subtype.coe_injective.comp Subtype.coe_injective) exponent hcardPre
  have hcardOver : Nat.card overgroup = Nat.card preimage :=
    (Nat.card_congr (preimage.equivMapOfInjective normalizer.subtype
      Subtype.coe_injective).toEquiv).symm
  have hLcount := (L.subgroupOf overgroup).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLover).toEquiv, hL] at hLcount
  change 192 * L.relIndex overgroup = Nat.card overgroup at hLcount
  have hintersection : Nat.card (L.subgroupOf K) = 64 := by
    rw [← Subgroup.inf_subgroupOf_left L K]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hKL]
  have hintersectionCount := (L.subgroupOf K).card_mul_index
  rw [hintersection, hK] at hintersectionCount
  change 64 * L.relIndex K = 192 at hintersectionCount
  have hindexLe : L.relIndex K ≤ L.relIndex overgroup :=
    Subgroup.relIndex_le_of_le_right hKover (by
      intro hzero
      rw [hzero, mul_zero] at hLcount
      exact Nat.card_pos.ne' hLcount.symm)
  omega
