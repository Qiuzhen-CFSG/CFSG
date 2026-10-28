module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.Contracts
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover
public import Mathlib.GroupTheory.Complement
public import Mathlib.Tactic.NormNum

/-!
# From local products to simultaneous Held pair conjugacy

After placing a pair in a candidate product, its inherited ambient Sylow
subgroup restricts to a Sylow subgroup of that product. The order-nine
subgroup is Sylow at three. Conjugate the odd subgroup first; the product
of the odd and even normalizers then adjusts the Sylow two-subgroup while
preserving the odd subgroup. Thus both subgroups, not just their join, are
carried to the published candidates by the same element.

The certified candidate orders discharge the marked two-group hypothesis
of the finite subgroup cover, giving unconditional local product coverage
and candidate permutability. The normalizer factorization follows from the
product decomposition. The source adapter uses these results to prove
exhaustive simultaneous conjugacy without a global order calculation for Held.

Sources: Aschbacher–Smith, printed pp.509–511; GLS3 Table 5.3p; the literal
candidate data in LocalActions/source/Explore.g and Explore.txt.
-/

public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
open Subgroup
open scoped Pointwise

private theorem sylow_pair_conjugate {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (S T : Sylow p G) (R U : Sylow q G)
    (hfactor : ∀ x : G, ∃ u ∈ normalizer (U : Set G),
      ∃ v ∈ normalizer (T : Set G), x = u * v) :
    ∃ g : G, (S : Subgroup G).map (MulAut.conj g).toMonoidHom = T ∧
      (R : Subgroup G).map (MulAut.conj g).toMonoidHom = U := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G R U
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq G T (a • S)
  obtain ⟨u, hu, v, hv, hb'⟩ := hfactor b
  have huU : u • U = U := Sylow.smul_eq_iff_mem_normalizer.mpr hu
  have hvT : v • T = T := Sylow.smul_eq_iff_mem_normalizer.mpr hv
  have haS : a • S = u • T := by rw [← hb, hb', mul_smul, hvT]
  have hS : (u⁻¹ * a) • S = T := by rw [mul_smul, haS, inv_smul_smul]
  have hR : (u⁻¹ * a) • R = U := by
    rw [mul_smul, ha]
    exact inv_smul_eq_iff.mpr huU.symm
  exact ⟨u⁻¹ * a, congrArg Sylow.toSubgroup hS, congrArg Sylow.toSubgroup hR⟩

private theorem map_subgroupOf_conj {G : Type*} [Group G]
    (K H : Subgroup G) (hH : H ≤ K) (g : K) :
    ((H.subgroupOf K).map (MulAut.conj g).toMonoidHom).map K.subtype =
      H.map (MulAut.conj (g : G)).toMonoidHom := by
  rw [map_map]
  have hc : K.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp K.subtype := rfl
  rw [hc, ← map_map, map_subgroupOf_eq_of_le hH]

private theorem mem_normalizer_subgroupOf {G : Type*} [Group G]
    (K H : Subgroup G) (g : K) (hg : (g : G) ∈ normalizer (H : Set G)) :
    g ∈ normalizer (H.subgroupOf K : Set K) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro x
  exact hg x

/-- The order certificate suffices to make every even candidate a two-group. -/
theorem candidateTwo_isPGroup (horders : CandidateOrders) (i : Bool) (j : Fin 2) :
    IsPGroup 2 (candidateTwo i j) :=
  IsPGroup.of_card (n := 10) (horders i j).1

private theorem candidate_complement (horders : CandidateOrders) (i : Bool) (j : Fin 2) :
    ((candidateOdd i j).subgroupOf (candidateProduct i j)).IsComplement'
      ((candidateTwo i j).subgroupOf (candidateProduct i j)) := by
  let K := candidateProduct i j
  have hR : candidateOdd i j ≤ K := le_sup_left
  have hT : candidateTwo i j ≤ K := le_sup_right
  have hcR : Nat.card ((candidateOdd i j).subgroupOf K) = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hR).toEquiv).trans (horders i j).2.1
  have hcT : Nat.card ((candidateTwo i j).subgroupOf K) = 1024 :=
    (Nat.card_congr (subgroupOfEquivOfLe hT).toEquiv).trans (horders i j).1
  have hcK : Nat.card K = 9216 := (horders i j).2.2
  exact isComplement'_of_coprime (by rw [hcR, hcT, hcK]) (by rw [hcR, hcT]; decide)

/-- Both candidate factors are actual Sylow complements inside their product.
This proves setwise permutability from cardinalities, without normality. -/
theorem candidate_permutes (horders : CandidateOrders) (i : Bool) (j : Fin 2) :
    (candidateOdd i j : Set He) * (candidateTwo i j : Set He) =
      (candidateTwo i j : Set He) * (candidateOdd i j : Set He) := by
  have hR : candidateOdd i j ≤ candidateProduct i j := le_sup_left
  have hT : candidateTwo i j ≤ candidateProduct i j := le_sup_right
  have hcomp := candidate_complement horders i j
  have he := congrArg (Set.image (candidateProduct i j).subtype)
    (hcomp.mul_eq.trans hcomp.symm.mul_eq.symm)
  simpa only [Set.image_mul, ← coe_map, map_subgroupOf_eq_of_le hR,
    map_subgroupOf_eq_of_le hT] using he

/-- The literal candidate factors form permuting odd/even pairs, with the
even factor a two-group. Both properties follow from the checked orders. -/
theorem candidate_pair_properties (i : Bool) (j : Fin 2) :
    IsPGroup 2 (candidateTwo i j) ∧
      (candidateOdd i j : Set He) * (candidateTwo i j : Set He) =
        (candidateTwo i j : Set He) * (candidateOdd i j : Set He) :=
  ⟨candidateTwo_isPGroup candidateOrders i j, candidate_permutes candidateOrders i j⟩

/-- Every local subgroup of odd relative index with prime divisors only two
and three is locally conjugate into one of the two literal candidate products.
The candidate-order and finite-cover certificates discharge every premise. -/
theorem localProductCover : LocalProductCover :=
  localProductCover_of_isPGroup (fun i => (candidate_pair_properties i 0).1)

/-- Permutability already supplies the normalizer factorization: an element
of either candidate factor normalizes that factor. No normalizer order or
orbit computation is needed. -/
theorem candidate_normalizer_factorization (horders : CandidateOrders) :
    NormalizerFactorization := by
  intro i j x hx
  obtain ⟨⟨u, v⟩, he⟩ := (candidate_complement horders i j).2 ⟨x, hx⟩
  exact ⟨u.val.val, u.val.property, le_normalizer u.property,
    v.val.val, v.val.property, le_normalizer v.property, (congrArg Subtype.val he).symm⟩

/-- An inherited ambient Sylow order makes every even candidate Sylow in
Held, without computing the order of Held itself. -/
theorem candidateTwo_sylow_of_sylow_card (horders : CandidateOrders)
    (S : Sylow 2 He) (hS : Nat.card S = 1024) (i : Bool) (j : Fin 2) :
    ∃ T : Sylow 2 He, (T : Subgroup He) = candidateTwo i j := by
  obtain ⟨T, hT⟩ := (candidateTwo_isPGroup horders i j).exists_le_sylow
  have hcT : Nat.card T = 1024 := (Nat.card_congr (T.equiv S).toEquiv).trans hS
  exact ⟨T, (eq_of_le_of_card_ge hT (by rw [hcT, (horders i j).1])).symm⟩

/-- Inside a candidate product, Sylow conjugacy and the verified relative
normalizer factorization simultaneously align the two members of a pair. -/
theorem pair_conjugate_in_candidate (horders : CandidateOrders)
    (i : Bool) (j : Fin 2)
    (S : Sylow 2 He) (R : Subgroup He)
    (hS : (S : Subgroup He) ≤ candidateProduct i j)
    (hR : R ≤ candidateProduct i j) (hcard : Nat.card R = 9) :
    ∃ g ∈ candidateProduct i j,
      (S : Subgroup He).map (MulAut.conj g).toMonoidHom = candidateTwo i j ∧
      R.map (MulAut.conj g).toMonoidHom = candidateOdd i j := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K := candidateProduct i j
  have hU : candidateOdd i j ≤ K := le_sup_left
  have hT : candidateTwo i j ≤ K := le_sup_right
  have hcK : Nat.card K = 9216 := (horders i j).2.2
  have hcR : Nat.card (R.subgroupOf K) = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hR).toEquiv).trans hcard
  have hcU : Nat.card ((candidateOdd i j).subgroupOf K) = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hU).toEquiv).trans (horders i j).2.1
  have hcT : Nat.card ((candidateTwo i j).subgroupOf K) = 1024 :=
    (Nat.card_congr (subgroupOfEquivOfLe hT).toEquiv).trans (horders i j).1
  let RP : Sylow 3 K := Sylow.ofCard (R.subgroupOf K) (by rw [hcR, hcK]; decide +kernel)
  let UP : Sylow 3 K := Sylow.ofCard ((candidateOdd i j).subgroupOf K)
    (by rw [hcU, hcK]; decide +kernel)
  let TP : Sylow 2 K := Sylow.ofCard ((candidateTwo i j).subgroupOf K)
    (by rw [hcT, hcK]; decide +kernel)
  have hf : ∀ x : K, ∃ u ∈ normalizer (UP : Set K),
      ∃ v ∈ normalizer (TP : Set K), x = u * v := by
    intro x
    obtain ⟨u, huK, hu, v, hvK, hv, he⟩ := candidate_normalizer_factorization horders i j x x.property
    exact ⟨⟨u, huK⟩, mem_normalizer_subgroupOf K _ ⟨u, huK⟩ hu,
      ⟨v, hvK⟩, mem_normalizer_subgroupOf K _ ⟨v, hvK⟩ hv, Subtype.ext he⟩
  obtain ⟨g, hgS, hgR⟩ := sylow_pair_conjugate (S.subtype hS) TP RP UP hf
  refine ⟨g, g.property, ?_, ?_⟩
  · have hm := congrArg (Subgroup.map K.subtype) hgS
    change (((S : Subgroup He).subgroupOf K).map
      (MulAut.conj g).toMonoidHom).map K.subtype =
        ((candidateTwo i j).subgroupOf K).map K.subtype at hm
    rwa [map_subgroupOf_conj K _ hS, map_subgroupOf_eq_of_le hT] at hm
  · have hm := congrArg (Subgroup.map K.subtype) hgR
    change ((R.subgroupOf K).map (MulAut.conj g).toMonoidHom).map K.subtype =
      ((candidateOdd i j).subgroupOf K).map K.subtype at hm
    rwa [map_subgroupOf_conj K _ hR, map_subgroupOf_eq_of_le hU] at hm

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
