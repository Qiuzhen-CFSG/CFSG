module
public import Theory.GroupTheory.TwoOrbitOddPrime.SectionCentralizer
public import Theory.SpecificGroups.PSL2.PairedOuterPrime

/-!
# Prime-to-p index of a pair of binary components

For two commuting normal factors with actual binary PSL₂ markings, the
ambient p-rank bound first makes the conjugation kernel p-prime. The split
field-image calculation then makes the index of their join p-prime. Pass
to the index-two component normalizer and then through the actual two-core
quotient to obtain the result for two nonnormal C-components.

Only odd primes dividing the component order are used. No condition on the
order of its entire outer automorphism group is assumed. The Chapter 10
consumer `HallGeometry.FieldComplement` applies the result to the original
M and L₀, proving coprimality of the Hall coefficient image and splitting
its kernel inside the original Hall carrier.

Source: Aschbacher--Smith 1.2.2(a), printed p.504, used by 10.1.3 and
10.2.3, printed pp.742,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.TwoOrbitOddPrime
open TwoOrbitThree
variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center A = ⊥) : center B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have h : e.symm x ∈ center A := ((centerCongr e).symm ⟨x,hx⟩).property
  have he : e.symm x = 1 := by simpa only [hz,mem_bot] using h
  exact e.symm.map_eq_one_iff.mp he


variable (L M : Subgroup G) [L.Normal] [M.Normal]

/-- The join of two marked binary factors has p-prime index. -/
theorem binary_join_index_coprime
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (eL : L ≃* Theory.PSL2.Group F) (eM : M ≃* Theory.PSL2.Group F)
    (hcomm : ⁅L,M⁆ = ⊥) (hL : center L = ⊥) (hM : center M = ⊥)
    (hdL : p ∣ Nat.card L) (hdM : p ∣ Nat.card M) (hr : primeRank p G ≤ 2) :
    Nat.Coprime p (L ⊔ M).index := by
  let a := markedAction L M eL eM
  have hC := pair_centralizer_coprime p L M hcomm hL hM hdL hdM hr
  have hk : Nat.Coprime p (Nat.card a.ker) := by rwa [markedAction_ker]
  have hrange : primeRank p a.range ≤ 2 := by
    apply (primeRank_le_of_surjective_of_coprime p a.rangeRestrict a.rangeRestrict_surjective ?_).trans hr
    simpa only [MonoidHom.ker_rangeRestrict] using hk
  have hI : (Theory.PSL2.inner F).prod (Theory.PSL2.inner F) ≤ a.range := by
    rw [show (Theory.PSL2.inner F).prod (Theory.PSL2.inner F) =
      (L ⊔ M).map a from (markedAction_map_join L M eL eM hcomm).symm]
    exact Subgroup.map_le_range _ _
  have ho := Theory.PSL2.PairedOuterPrime.quotient_by_inner_preimage_coprime F p a hI hrange
    (by rwa [←Nat.card_congr eL.toEquiv])
  change Nat.Coprime p (((MulAut.innerSubgroup (Theory.PSL2.Group F)).prod
    (MulAut.innerSubgroup (Theory.PSL2.Group F))).comap a).index at ho
  rw [markedAction_comap_inner L M eL eM hcomm] at ho
  rw [←relIndex_mul_index (show L ⊔ M ≤ L ⊔ M ⊔ centralizer ((L ⊔ M : Subgroup G) : Set G) from le_sup_left)]
  exact (hC.coprime_dvd_right (by rw [relIndex_sup_left]; exact relIndex_dvd_card _ _)).mul_right ho


omit [L.Normal] [M.Normal] in
/-- Index two contributes no odd prime to the component-pair index. -/
theorem binary_pair_index_coprime
    (hp : p ≠ 2) (hi : (normalizer (L : Set G)).index = 2) (t : G) (hc : ⁅L,L.conjBy t⁆ = ⊥)
    (hz : center L = ⊥) (hd : p ∣ Nat.card L) (hr : primeRank p G ≤ 2)
    (F : Type*) [Field F] [Finite F] [CharP F 2] (e : L ≃* Theory.PSL2.Group F) :
    Nat.Coprime p (L ⊔ L.conjBy t).index := by
  let N := normalizer (L : Set G)
  let : N.Normal := N.normal_of_index_eq_two hi
  let A := L.subgroupOf N
  let B := (L.conjBy t).subgroupOf N
  have hB := conjugate_le_normalizer_of_index_two L hi t
  let eA : A ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let eB : B ≃* L := (subgroupOfEquivOfLe hB).trans ((MulAut.conj t).subgroupMap L).symm
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (normalizes_conjugate_of_normalizes
      (show t ∈ normalizer (N : Set G) from N.normalizer_eq_top ▸ mem_top t) le_rfl)
  have hzA : center A = ⊥ := center_bot_transport eA.symm hz
  have hzB : center B = ⊥ := center_bot_transport eB.symm hz
  have hdA : p ∣ Nat.card A := by rwa [Nat.card_congr eA.toEquiv]
  have hdB : p ∣ Nat.card B := by rwa [Nat.card_congr eB.toEquiv]
  have hcAB : ⁅A,B⁆ = ⊥ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le L.le_normalizer,
      map_subgroupOf_eq_of_le hB,hc,Subgroup.map_bot]
  have hindex := binary_join_index_coprime p A B F (eA.trans e) (eB.trans e)
    hcAB hzA hzB hdA hdB ((primeRank_subgroup_le p N).trans hr)
  have hLN := sup_le L.le_normalizer hB
  have he : (L ⊔ L.conjBy t).subgroupOf N = A ⊔ B := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hLN,Subgroup.map_sup,
      map_subgroupOf_eq_of_le L.le_normalizer,map_subgroupOf_eq_of_le hB]
  rw [←he] at hindex
  rw [←relIndex_mul_index hLN,hi]
  exact hindex.mul_right ((Fact.out : p.Prime).odd_of_ne_two hp).coprime_two_right

omit [L.Normal] [M.Normal] in
/-- The same index bound lifts through the literal ambient two-core. -/
theorem binary_cComponent_pair_index_coprime (hp : p ≠ 2)
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (ht : t ∉ normalizer (L : Set G))
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) (hr : primeRank p G ≤ 2)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) :
    Nat.Coprime p (L ⊔ L.conjBy t).index := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let eB := cComponentTwoCoreQuotientEquiv hL
  let : (L ⊔ L.conjBy t).Normal := TwoOrbitThree.pair_normal_of_index_two L hi t ht
  have hindex := binary_pair_index_coprime p B hp
    ((cComponent_normalizer_index_quotient hL _).trans hi) (q t)
    (TwoOrbitThree.quotient_pair_commutes hL t ht) (center_bot_transport eB hz)
    (by rwa [←Nat.card_congr eB.toEquiv])
    ((primeRank_quotient_le_of_isTwoGroup p ((Fact.out : p.Prime).odd_of_ne_two hp)
      _ pCore_isPGroup).trans hr)
    F (eB.symm.trans e)
  rw [←TwoOrbitThree.pair_map_quotient L t,index_map,QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),index_top,mul_one] at hindex
  have hp2 : Nat.Coprime p 2 := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => hp ((Nat.prime_two.eq_one_or_self_of_dvd p h).resolve_left
      (Fact.out : p.Prime).ne_one))
  have hcore : Nat.Coprime p (Nat.card (pCore 2 G)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_dvd_pow
    exact (hp2.pow_right n).coprime_dvd_right hn
  rw [←relIndex_mul_index (show L ⊔ L.conjBy t ≤ L ⊔ L.conjBy t ⊔ pCore 2 G from le_sup_left)]
  apply Nat.Coprime.mul_right _ hindex
  rw [relIndex_sup_left]
  exact hcore.coprime_dvd_right (relIndex_dvd_card _ _)

end Theory.GroupTheory.TwoOrbitOddPrime
