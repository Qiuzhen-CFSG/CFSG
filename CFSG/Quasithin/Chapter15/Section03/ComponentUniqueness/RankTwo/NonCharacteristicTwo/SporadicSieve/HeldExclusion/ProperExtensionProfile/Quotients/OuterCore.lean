module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.PureActor
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Mathlib.GroupTheory.Complement

/-!
# The pure-pair normalizer acquires no outer two-core elements

The inner pure product is the setwise product of its order-nine and order-1024
factors, by the checked cardinalities. An outer pointwise fixer of the odd factor
would therefore give a quarter-turn induced by an element of the two-factor.
The existing orbit-color certificate rules this out. Hence the odd factor's
centralizer in the full normalizer lies in the inner part.

For Q=O₂(N), coprime action gives Q=[Q,R] C_Q(R). The inner part is normal and
contains R, so both factors are inner. This proves that O₂(N) is entirely inner,
without computing its order or assuming the pure product's core structure.

Source: GLS3 Table 5.3p; the checked PureActors and InnerImages for the unchanged
Held carrier; Aschbacher--Smith 15.3.41--42, printed p.1138.
-/

public section
open Subgroup Theory.GroupTheory Held.LocalPairs
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
open Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages

private theorem pureProduct_factors (b : Held.He) (hb : b ∈ innerLocal true) :
    ∃ r ∈ candidateOdd false 0, ∃ s ∈ candidateTwo false 0, b = r * s := by
  let B := innerLocal true
  let R := (candidateOdd false 0).subgroupOf B
  let S := (candidateTwo false 0).subgroupOf B
  have hR : candidateOdd false 0 ≤ B := le_sup_left
  have hS : candidateTwo false 0 ≤ B := le_sup_right
  have hcR : Nat.card R = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hR).toEquiv).trans
      (Exhaustion.candidateOrders false 0).2.1
  have hcS : Nat.card S = 1024 :=
    (Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv).trans
      (Exhaustion.candidateOrders false 0).1
  have hcB : Nat.card B = 9216 := (Exhaustion.candidateOrders false 0).2.2
  have hcomp : R.IsComplement' S :=
    isComplement'_of_coprime (by rw [hcR, hcS, hcB]) (by rw [hcR, hcS]; decide)
  obtain ⟨⟨r, s⟩, h⟩ := hcomp.2 ⟨b, hb⟩
  exact ⟨r.val, r.property, s.val, s.property, (congrArg Subtype.val h).symm⟩

private theorem odd_commute (r y : Held.He)
    (hr : r ∈ candidateOdd false 0) (hy : y ∈ candidateOdd false 0) : r * y = y * r := by
  have h : (⟨r, hr⟩ : candidateOdd false 0) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨r, hr⟩ := by
    apply (candidateOddEquiv false 0).injective
    simp only [map_mul, mul_comm]
  exact congrArg Subtype.val h

/-- A pointwise fixer of the marked odd factor cannot belong to the outer coset.
Factor its inner part as an odd element times a two-element; the latter would
induce a quarter-turn on the marked plane, contradicting the checked color bound. -/
theorem pure_fixer_is_inner
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (a : MulAut Held.He) (ha : a ∈ candidate true)
    (hfix : ∀ r ∈ candidateOdd false 0, a r = r) : a ∈ MulAut.innerSubgroup Held.He := by
  by_contra hout
  let I := (MulAut.innerSubgroup Held.He).subgroupOf (candidate true)
  let aa : candidate true := ⟨a, ha⟩
  let t : candidate true := ⟨pureAutomorphism, pureAutomorphism_mem⟩
  have ht : t⁻¹ ∉ I := by
    intro h
    exact pureAutomorphism_not_inner (I.inv_mem h)
  have hp : aa * t⁻¹ ∈ I :=
    (mul_mem_iff_of_index_two (candidate_true_inner_index hreal hbound)).mpr
      (iff_of_false hout ht)
  obtain ⟨b, hb⟩ := hp
  have hbn : b ∈ normalizer (innerLocal true : Set Held.He) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hb]
    exact (aa * t⁻¹).property
  have hbB : b ∈ innerLocal true := by rwa [innerLocal_self_normalizing] at hbn
  have hab : a = MulAut.conj b * pureAutomorphism := by
    change MulAut.conj b = a * pureAutomorphism⁻¹ at hb
    exact (mul_inv_eq_iff_eq_mul.mp hb.symm)
  obtain ⟨r, hr, s, hs, rfl⟩ := pureProduct_factors b hbB
  apply PureActors.coordinateAction_not_mem_diagonal false
  apply InnerImages.mem_diagonal_of_vectors
  intro k
  apply InnerImages.coordinates_of_conjugation false 0 k s⁻¹
    ((candidateTwo false 0).inv_mem hs)
  rw [InnerImages.markedEmbedding_eq, PureActors.candidateOddEquiv_symm_image]
  have him : pureAutomorphism (basisGenerator false 0 k) = PureActors.imageElement false k := by
    apply Held.representation_injective
    exact PureActors.actor_conj_basis false k
  have hf := hfix _ (basisGenerator_mem false 0 k)
  rw [hab] at hf
  have hrfix : r * basisGenerator false 0 k * r⁻¹ = basisGenerator false 0 k := by
    rw [odd_commute r _ hr (basisGenerator_mem false 0 k), mul_inv_cancel_right]
  have hsfix : s * PureActors.imageElement false k * s⁻¹ = basisGenerator false 0 k := by
    apply (MulAut.conj r).injective
    change r * (s * PureActors.imageElement false k * s⁻¹) * r⁻¹ =
      r * basisGenerator false 0 k * r⁻¹
    rw [hrfix]
    change (r * s) * pureAutomorphism (basisGenerator false 0 k) * (r * s)⁻¹ = _ at hf
    simpa only [him, mul_inv_rev, mul_assoc] using hf
  rw [← hsfix]
  group

/-- The actual odd factor, embedded by the inner action into the full normalizer. -/
@[expose] def pureOdd : Subgroup (candidate true) :=
  ((candidateOdd false 0).map (MulAut.conj : Held.He →* MulAut Held.He)).subgroupOf (candidate true)

private theorem odd_image_le_candidate :
    (candidateOdd false 0).map (MulAut.conj : Held.He →* MulAut Held.He) ≤ candidate true := by
  rintro _ ⟨r, hr, rfl⟩
  exact mem_normalizer_iff_map_conj_eq.mp
    ((innerLocal true).le_normalizer (show r ∈ innerLocal true from (show candidateOdd false 0 ≤ innerLocal true from le_sup_left) hr))

/-- The embedded marked odd factor still has order nine. -/
theorem pureOdd_card : Nat.card pureOdd = 9 := by
  rw [pureOdd, Nat.card_congr (subgroupOfEquivOfLe odd_image_le_candidate).toEquiv,
    card_map_of_injective (conj_injective_of_center_eq_bot Held.LocalPairs.center_eq_bot)]
  exact (Exhaustion.candidateOrders false 0).2.1

/-- The marked odd factor consists of actual inner automorphisms. -/
theorem pureOdd_le_inner : pureOdd ≤ (MulAut.innerSubgroup Held.He).subgroupOf (candidate true) := by
  rintro a ⟨r, _, hr⟩
  exact ⟨r, hr⟩

/-- Centerlessness identifies centralization of the inner odd subgroup with
pointwise fixation of the literal odd subgroup of Held. -/
theorem pureOdd_centralizer_le_inner
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    centralizer (pureOdd : Set (candidate true)) ≤
      (MulAut.innerSubgroup Held.He).subgroupOf (candidate true) := by
  intro a ha
  apply pure_fixer_is_inner hreal hbound a.val a.property
  intro r hr
  let rr : candidate true := ⟨MulAut.conj r, odd_image_le_candidate ⟨r, hr, rfl⟩⟩
  have hh := congrArg Subtype.val (ha rr (show rr ∈ pureOdd from ⟨r, hr, rfl⟩))
  have he : MulAut.conj (a.val r) = MulAut.conj r := by
    have hmul : MulAut.conj (a.val r) * a.val = a.val * MulAut.conj r := by
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    apply mul_right_cancel (b := a.val)
    exact hmul.trans hh.symm
  exact conj_injective_of_center_eq_bot Held.LocalPairs.center_eq_bot he

/-- Coprime decomposition excludes every outer element from the intrinsic
two-core: the commutator factor and the odd centralizer are both inner. -/
theorem candidate_true_core_le_inner
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    pCore 2 (candidate true) ≤ (MulAut.innerSubgroup Held.He).subgroupOf (candidate true) := by
  let Q := pCore 2 (candidate true)
  let I := (MulAut.innerSubgroup Held.He).subgroupOf (candidate true)
  have hp : IsPGroup 2 Q := pCore_isPGroup
  let := hp.isNilpotent
  have hcop : Nat.Coprime (Nat.card pureOdd) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [pureOdd_card, hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  have he := eq_commutator_sup_centralizer_of_solvable_coprime Q pureOdd
    le_normalizer_of_normal inferInstance hcop
  change Q ≤ I
  rw [he]
  exact sup_le ((commutator_mono le_rfl pureOdd_le_inner).trans (commutator_le_right Q I))
    (inf_le_right.trans (pureOdd_centralizer_le_inner hreal hbound))


end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
