module
public import Theory.GroupTheory.TwoOrbitThree.PairedAction
public import Theory.GroupTheory.IndexTwoConjugatePair
/-!
# Passing from the component normalizer to the two-element orbit

A component with normalizer of index two has two conjugates; their join
is normal in the full group. Both individual factors are normal in the
original normalizer. Restricting the literal conjugation action there
and multiplying the relative index by two turns the paired automorphism
calculation into a three-prime index for the full orbit product.
Source: Aschbacher--Smith 1.2.2(a), printed p.504, 1 March 2004.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.GroupTheory.TwoOrbitThree
variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

omit [Finite G] in
theorem conjugate_le_normalizer_of_index_two
    (hi : (normalizer (L : Set G)).index = 2) (t : G) : L.conjBy t ≤ normalizer (L : Set G) := by
  let N := normalizer (L : Set G)
  let : N.Normal := N.normal_of_index_eq_two hi
  rintro x ⟨l,hl,rfl⟩
  exact (inferInstance : N.Normal).conj_mem l (L.le_normalizer hl) t

omit [Finite G] in
theorem pair_normal_of_index_two (hi : (normalizer (L : Set G)).index = 2)
    (t : G) (ht : t ∉ normalizer (L : Set G)) : (L ⊔ L.conjBy t).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  have hc (g : G) : L.conjBy g = L ∨ L.conjBy g = L.conjBy t := by
    by_cases hg : g ∈ normalizer (L : Set G)
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hg)
    · have he : t⁻¹ * g ∈ normalizer (L : Set G) :=
        (mul_mem_iff_of_index_two hi).mpr (by simp [ht,hg])
      have hh := congrArg (fun B : Subgroup G => B.conjBy t)
        (mem_normalizer_iff_map_conj_eq.mp he)
      change (L.conjBy (t⁻¹*g)).conjBy t = _ at hh
      rw [conjBy_mul,conjBy_inv'] at hh
      exact Or.inr hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm
  · rw [Subgroup.map_sup]
    apply sup_le
    · change L.conjBy g ≤ _
      rcases hc g with he | he <;> rw [he]
      · exact le_sup_left
      · exact le_sup_right
    · change (L.conjBy t).conjBy g ≤ _
      rw [conjBy_conjBy]
      rcases hc (g*t) with he | he <;> rw [he]
      · exact le_sup_left
      · exact le_sup_right
  · have hle : (L ⊔ L.conjBy t).map (MulAut.conj g⁻¹).toMonoidHom ≤ L ⊔ L.conjBy t := by
      rw [Subgroup.map_sup]
      apply sup_le
      · change L.conjBy g⁻¹ ≤ _
        rcases hc g⁻¹ with he | he <;> rw [he]
        · exact le_sup_left
        · exact le_sup_right
      · change (L.conjBy t).conjBy g⁻¹ ≤ _
        rw [conjBy_conjBy]
        rcases hc (g⁻¹*t) with he | he <;> rw [he]
        · exact le_sup_left
        · exact le_sup_right
    have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hle
    change ((L ⊔ L.conjBy t).conjBy g⁻¹).conjBy g ≤ _ at hmap
    rwa [conjBy_inv'] at hmap

omit [Finite G] in
theorem pair_index_coprime_three_of_normalizer
    (hi : (normalizer (L : Set G)).index = 2) (t : G)
    (hindex : Nat.Coprime 3 ((L.subgroupOf (normalizer (L : Set G))) ⊔
      ((L.conjBy t).subgroupOf (normalizer (L : Set G)))).index) :
    Nat.Coprime 3 (L ⊔ L.conjBy t).index := by
  have hLN := sup_le L.le_normalizer (conjugate_le_normalizer_of_index_two L hi t)
  have he : (L ⊔ L.conjBy t).subgroupOf (normalizer (L : Set G)) =
      L.subgroupOf (normalizer (L : Set G)) ⊔ (L.conjBy t).subgroupOf (normalizer (L : Set G)) := by
    apply map_injective (normalizer (L : Set G)).subtype_injective
    rw [map_subgroupOf_eq_of_le hLN,Subgroup.map_sup,
      map_subgroupOf_eq_of_le L.le_normalizer,
      map_subgroupOf_eq_of_le (conjugate_le_normalizer_of_index_two L hi t)]
  rw [←he] at hindex
  rw [←relIndex_mul_index hLN,hi]
  exact hindex.mul_right (by decide)

private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center A = ⊥) : center B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have h : e.symm x ∈ center A := ((centerCongr e).symm ⟨x,hx⟩).property
  have he : e.symm x = 1 := by simpa only [hz,mem_bot] using h
  exact e.symm.map_eq_one_iff.mp he

omit [Finite G] in
private theorem pair_normalizer_commutator
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (hc : ⁅L,L.conjBy t⁆ = ⊥) :
    ⁅L.subgroupOf (normalizer (L : Set G)),
      (L.conjBy t).subgroupOf (normalizer (L : Set G))⁆ = ⊥ := by
  apply map_injective (normalizer (L : Set G)).subtype_injective
  rw [map_commutator,map_subgroupOf_eq_of_le L.le_normalizer,
    map_subgroupOf_eq_of_le (conjugate_le_normalizer_of_index_two L hi t),hc,Subgroup.map_bot]

theorem binary_pair_index_coprime_three
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (hc : ⁅L,L.conjBy t⁆ = ⊥)
    (hz : center L = ⊥) (hd : 3 ∣ Nat.card L) (hr : primeRank 3 G ≤ 2)
    (F : Type*) [Field F] [Finite F] [CharP F 2] (e : L ≃* Theory.PSL2.Group F) :
    Nat.Coprime 3 (L ⊔ L.conjBy t).index := by
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
  have hdA : 3 ∣ Nat.card A := by rwa [Nat.card_congr eA.toEquiv]
  have hdB : 3 ∣ Nat.card B := by rwa [Nat.card_congr eB.toEquiv]
  exact pair_index_coprime_three_of_normalizer L hi t
    (binary_join_index_coprime_three A B F (eA.trans e) (eB.trans e)
      (pair_normalizer_commutator L hi t hc) hzA hzB hdA hdB
      ((primeRank_subgroup_le 3 N).trans hr))

theorem outer_pair_index_coprime_three
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (hc : ⁅L,L.conjBy t⁆ = ⊥)
    (hz : center L = ⊥) (hd : 3 ∣ Nat.card L) (hr : primeRank 3 G ≤ 2)
    (ho : Nat.Coprime 3 (MulAut.innerSubgroup L).index) :
    Nat.Coprime 3 (L ⊔ L.conjBy t).index := by
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
  have hdA : 3 ∣ Nat.card A := by rwa [Nat.card_congr eA.toEquiv]
  have hdB : 3 ∣ Nat.card B := by rwa [Nat.card_congr eB.toEquiv]
  have hoA : Nat.Coprime 3 (MulAut.innerSubgroup A).index := by
    change Nat.Coprime 3 (Nat.card (MulAut.Outer A))
    rw [Nat.card_congr (MulAut.outerCongr eA).toEquiv]
    exact ho
  have hoB : Nat.Coprime 3 (MulAut.innerSubgroup B).index := by
    change Nat.Coprime 3 (Nat.card (MulAut.Outer B))
    rw [Nat.card_congr (MulAut.outerCongr eB).toEquiv]
    exact ho
  exact pair_index_coprime_three_of_normalizer L hi t
    (outer_join_index_coprime_three A B (pair_normalizer_commutator L hi t hc)
      hzA hzB hdA hdB ((primeRank_subgroup_le 3 N).trans hr) hoA hoB)

end Theory.GroupTheory.TwoOrbitThree
