module

public import Theory.Character.ModularBlock.MixedConjugationTrace
public import Theory.Character.ModularBlock.CompatibleSelectorComplex
public import Theory.Character.ModularBlock.PrincipalKernel
public import Theory.Character.ModularBlock.MixedBrauerTrace

/-!
# Local principal-block values and normal complements

Mixed Brauer trace comparison implies equality of principal-block character
columns on a two-section after multiplication by the local odd core. Indeed,
the local odd core acts trivially on every local principal-block character,
so all four inner products of the two columns agree. Positivity then makes
their squared distance zero. A normal two-complement places every odd-order
centralizer element in the local odd core.

The mixed trace comparison is supplied by `MixedBrauerTrace` for arbitrary
two-elements. This gives the local section identity and its normal-complement
specialization, including the case where the two-element is the identity.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 3.8, p. 88.
-/

public section
noncomputable section

namespace ModularBlock.NormalComplementValues

open scoped BigOperators
open PrincipalBlockConstruction BlockOrthogonality CompatibleBrauerBlock
open MixedConjugationTrace

variable {G : Type*} [Group G] [Finite G]

private theorem eq_of_four_inner_products_eq
    {I : Type*} (s : Finset I) (f g : I → ℂ) (c : ℂ)
    (hff : ∑ i ∈ s, f i * star (f i) = c)
    (hfg : ∑ i ∈ s, f i * star (g i) = c)
    (hgf : ∑ i ∈ s, g i * star (f i) = c)
    (hgg : ∑ i ∈ s, g i * star (g i) = c)
    {i : I} (hi : i ∈ s) : f i = g i := by
  have hz : ∑ j ∈ s, (f j - g j) * star (f j - g j) = 0 := by
    simp only [star_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
    rw [hff, hgf, hfg, hgg]
    ring
  have hr : ∑ j ∈ s, Complex.normSq (f j - g j) = 0 := by
    have h := congrArg Complex.re hz
    simpa only [Complex.re_sum, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_re, Complex.zero_re] using h
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (f j - g j))).mp hr i hi))

/-- A mixed local trace comparison on the odd core implies the full
characterwise local section identity. No restriction on the order of `u`
is needed for this implication; the two-element hypothesis belongs to the
mixed Brauer trace theorem supplying `htrace`. -/
theorem character_mul_right_eq_of_local_mixed_trace
    (d : PrincipalCongruenceBlockData G) (u : G)
    (htrace : ∀ v w : Subgroup.centralizer ({u} : Set G),
      v ∈ pPrimeCore 2 (Subgroup.centralizer ({u} : Set G)) →
      w ∈ pPrimeCore 2 (Subgroup.centralizer ({u} : Set G)) →
      LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedLeftRight (principalBlockElement d) (u * v) (u * w)) =
      LinearMap.trace ℂ
        (MonoidAlgebra ℂ (Subgroup.centralizer ({u} : Set G)))
        (projectedLeftRight
          (principalBlockElement (localData d (Subgroup.centralizer ({u} : Set G))))
          v w))
    {i : d.I} (hi : i ∈ d.block)
    (v : Subgroup.centralizer ({u} : Set G))
    (hv : v ∈ pPrimeCore 2 (Subgroup.centralizer ({u} : Set G))) :
    d.chi i (ConjClasses.mk (u * v)) = d.chi i (ConjClasses.mk u) := by
  classical
  let l := localData d (Subgroup.centralizer ({u} : Set G))
  let c : ℂ := ∑ j ∈ l.block, l.chi j (ConjClasses.mk 1) *
    star (l.chi j (ConjClasses.mk 1))
  have hinner (a b : Subgroup.centralizer ({u} : Set G))
      (ha : a ∈ pPrimeCore 2 (Subgroup.centralizer ({u} : Set G)))
      (hb : b ∈ pPrimeCore 2 (Subgroup.centralizer ({u} : Set G))) :
      ∑ j ∈ d.block, d.chi j (ConjClasses.mk (u * a)) *
        star (d.chi j (ConjClasses.mk (u * b))) = c := by
    have h := htrace a b ha hb
    rw [principalBlock_leftRight_trace, principalBlock_leftRight_trace] at h
    refine h.trans (Finset.sum_congr rfl (fun j hj => ?_))
    have hval (x : Subgroup.centralizer ({u} : Set G))
        (hx : x ∈ pPrimeCore 2 (Subgroup.centralizer ({u} : Set G))) :
        l.chi j (ConjClasses.mk x) = l.chi j (ConjClasses.mk 1) := by
      simpa only [one_mul] using
        PrincipalBlockKernel.character_mul_right_eq_of_mem_block l hj 1 x hx
    rw [hval a ha, hval b hb]
  have h1 : (1 : Subgroup.centralizer ({u} : Set G)) ∈
      pPrimeCore 2 (Subgroup.centralizer ({u} : Set G)) := Subgroup.one_mem _
  apply eq_of_four_inner_products_eq d.block
    (fun j => d.chi j (ConjClasses.mk (u * v)))
    (fun j => d.chi j (ConjClasses.mk u)) c
    (hinner v v hv hv) _ _ _ hi
  · simpa only [Subgroup.coe_one, mul_one] using hinner v 1 hv h1
  · simpa only [Subgroup.coe_one, mul_one] using hinner 1 v h1 hv
  · simpa only [Subgroup.coe_one, mul_one] using hinner 1 1 h1 h1

/-- Normal-complement reduction of the requested local principal-block
identity, with the mixed Brauer trace input kept explicit. -/
theorem principal_value_mul_eq_of_normal_two_complement_of_local_mixed_trace
    (d : PrincipalCongruenceBlockData G) (u v : G)
    (N : Subgroup (Subgroup.centralizer ({u} : Set G))) [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N))
    (hquot : IsPGroup 2 ((Subgroup.centralizer ({u} : Set G)) ⧸ N))
    (huv : Commute u v) (hv : Nat.Coprime 2 (orderOf v))
    (htrace : ∀ a b : Subgroup.centralizer ({u} : Set G),
      a ∈ pPrimeCore 2 (Subgroup.centralizer ({u} : Set G)) →
      b ∈ pPrimeCore 2 (Subgroup.centralizer ({u} : Set G)) →
      LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedLeftRight (principalBlockElement d) (u * a) (u * b)) =
      LinearMap.trace ℂ
        (MonoidAlgebra ℂ (Subgroup.centralizer ({u} : Set G)))
        (projectedLeftRight
          (principalBlockElement (localData d (Subgroup.centralizer ({u} : Set G))))
          a b))
    {i : d.I} (hi : i ∈ d.block) :
    d.chi i (ConjClasses.mk (u * v)) = d.chi i (ConjClasses.mk u) := by
  let vC : Subgroup.centralizer ({u} : Set G) :=
    ⟨v, Subgroup.mem_centralizer_singleton_iff.mpr huv.symm.eq⟩
  exact character_mul_right_eq_of_local_mixed_trace d u htrace hi vC
    (mem_pPrimeCore_of_normal_complement N hN hquot vC
      (by simpa only [vC, Subgroup.orderOf_mk] using hv))

/-- Principal-block character values on a two-section are unchanged by
multiplication by an element of the centralizer's odd core. -/
theorem character_mul_right_eq_of_mem_local_pPrimeCore
    (d : PrincipalCongruenceBlockData G) (u : G)
    (hu : ∃ k : ℕ, u ^ (2 ^ k) = 1)
    {i : d.I} (hi : i ∈ d.block)
    (v : Subgroup.centralizer ({u} : Set G))
    (hv : v ∈ pPrimeCore 2 (Subgroup.centralizer ({u} : Set G))) :
    d.chi i (ConjClasses.mk (u * v)) = d.chi i (ConjClasses.mk u) := by
  apply character_mul_right_eq_of_local_mixed_trace d u _ hi v hv
  intro a b ha hb
  exact MixedBrauerTrace.principalBlock_mixed_trace_eq_of_pPrimeCore
    d u hu ⟨a, ha⟩ ⟨b, hb⟩

/-- The local principal-block identity of Glauberman's Lemma 3.8: an odd-order
element commuting with a two-element can be removed from character values
when the centralizer has a normal two-complement. -/
theorem principal_value_mul_eq_of_normal_two_complement
    (d : PrincipalCongruenceBlockData G) (u v : G)
    (hu : ∃ k : ℕ, u ^ (2 ^ k) = 1)
    (N : Subgroup (Subgroup.centralizer ({u} : Set G))) [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N))
    (hquot : IsPGroup 2 ((Subgroup.centralizer ({u} : Set G)) ⧸ N))
    (huv : Commute u v) (hv : Nat.Coprime 2 (orderOf v))
    {i : d.I} (hi : i ∈ d.block) :
    d.chi i (ConjClasses.mk (u * v)) = d.chi i (ConjClasses.mk u) := by
  apply principal_value_mul_eq_of_normal_two_complement_of_local_mixed_trace
    d u v N hN hquot huv hv _ hi
  intro a b ha hb
  exact MixedBrauerTrace.principalBlock_mixed_trace_eq_of_pPrimeCore
    d u hu ⟨a, ha⟩ ⟨b, hb⟩

end ModularBlock.NormalComplementValues
