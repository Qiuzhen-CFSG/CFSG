module

public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-!
# Normalizer actions in an elementary TI-pair

Write `U = V ∩ N(A)`, `B = A ∩ N(V)`, `X = ⟨V, A⟩`, and `Y = U B`.
For disjoint elementary abelian 2-subgroups that are TI, involution commutators
show that `X` normalizes `Y`. The TI centralizer criterion gives `C_Y(v) = U`
for `v ∈ V − U`. The map `b ↦ [b, v]` injects `B` into `U`; applying this
symmetrically, with a separate cardinal bound when a normalizer is full, proves
`|U| = |B|`. The same map is then surjective and yields `[Y, ⟨v⟩] = U`.

Equal rank is used in its equivalent finite elementary-abelian form
`Nat.card V = Nat.card A`. The source's distinctness and cross-conjugate
hypothesis imply disjointness by `ti_pair_disjoint_of_distinct`. Nontriviality
of `U` is not needed for these action statements. Normality is relative to `X`,
and the centralizer and commutator equalities retain the ambient embeddings.
The symmetric statements use the same subgroup `Y`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma I.6.2(2a) and its proof, printed pp. 424--425.
-/

@[expose] public section

open scoped commutatorElement
namespace CFSG.Quasithin.ChapterI.Section06To08

variable {G : Type*} [Group G]

private theorem elementary_inv (A : Subgroup G) [IsElementaryAbelian 2 A]
    {a : G} (ha : a ∈ A) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using
    elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)

/-- An involution in the mutual normalizer has its commutators in the opposite
mutual normalizer. -/
theorem ti_pair_commutator_mem_opposite (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V)
    {u a : G} (hu : u ∈ V ⊓ Subgroup.normalizer (A : Set G)) (ha : a ∈ A) :
    ⁅a, u⁆ ∈ A ⊓ Subgroup.normalizer (V : Set G) := by
  have hcA : ⁅a, u⁆ ∈ A := by
    change a * u * a⁻¹ * u⁻¹ ∈ A
    simpa only [mul_assoc] using A.mul_mem ha
      ((Subgroup.mem_normalizer_iff.mp hu.2 a⁻¹).mp (A.inv_mem ha))
  by_cases hu1 : u = 1
  · simp [hu1]
  have hui := elementary_inv V hu.1
  have hci := elementary_inv A hcA
  have hc : Commute ⁅a, u⁆ u := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      ⁅a, u⁆ * u * ⁅a, u⁆⁻¹ = ⁅a, u⁆ * u * ⁅a, u⁆ := by rw [hci]
      _ = a * (u * u) * a⁻¹ * u⁻¹ := by
        simp only [commutatorElement_def]; group
      _ = u := by
        rw [show u * u = 1 by simpa only [pow_two] using
          elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu.1]
        simp [hui]
  rw [ti_pair_opposite_normalizer_eq_centralizer V A hVA hV hu.1 hu.2 hu1]
  exact ⟨hcA, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩

private theorem pair_product (V A : Subgroup G) (hVA : Disjoint V A)
    {y : G} (hy : y ∈ (V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G))) :
    ∃ u ∈ V ⊓ Subgroup.normalizer (A : Set G),
      ∃ b ∈ A ⊓ Subgroup.normalizer (V : Set G), y = u * b := by
  obtain ⟨e, he⟩ := ti_pair_mutual_normalizers_mulEquiv V A hVA
  obtain ⟨⟨u, b⟩, hab⟩ := e.surjective ⟨y, hy⟩
  exact ⟨u, u.property, b, b.property, (congrArg Subtype.val hab).symm.trans (he u b)⟩

private theorem pair_left_normalizes (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hA : IsTISubgroup A) :
    V ≤ Subgroup.normalizer (((V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G)) : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro v hv y hy
  obtain ⟨u, hu, b, hb, rfl⟩ := pair_product V A hVA hy
  have hc := ti_pair_commutator_mem_opposite A V hVA.symm hA hb hv
  have hvu : Commute v u := setLike_mul_comm hv hu.1
  have heq : v * (u * b) * v⁻¹ = u * ⁅v, b⁆ * b := by
    rw [commutatorElement_def]
    calc
      _ = (v * u) * b * v⁻¹ := by group
      _ = (u * v) * b * v⁻¹ := by rw [hvu.eq]
      _ = _ := by group
  rw [heq]
  exact Subgroup.mul_mem_sup ((V ⊓ Subgroup.normalizer (A : Set G)).mul_mem hu hc) hb

/-- The product of the mutual normalizers is invariant under the generated pair. -/
theorem ti_pair_sup_le_normalizer (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A) :
    V ⊔ A ≤ Subgroup.normalizer (((V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G)) : Subgroup G) : Set G) := by
  apply sup_le
  · exact pair_left_normalizes V A hVA hA
  · simpa only [sup_comm] using pair_left_normalizes A V hVA.symm hV

/-- An element of `V` outside its mutual normalizer fixes exactly `U` in `Y`. -/
theorem ti_pair_centralizer_eq (V A : Subgroup G)
    [IsElementaryAbelian 2 V] (hVA : Disjoint V A) (hA : IsTISubgroup A)
    {v : G} (hv : v ∈ V) (hvU : v ∉ V ⊓ Subgroup.normalizer (A : Set G)) :
    ((V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G))) ⊓ Subgroup.centralizer ({v} : Set G) =
      V ⊓ Subgroup.normalizer (A : Set G) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨u, hu, b, hb, rfl⟩ := pair_product V A hVA hy.1
    have hvu : Commute v u := setLike_mul_comm hv hu.1
    have hvub : Commute v (u * b) :=
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
    have hvb : Commute v b := by
      change v * b = b * v
      apply mul_left_cancel (a := u)
      calc
        u * (v * b) = v * (u * b) := by rw [← mul_assoc, ← hvu.eq, mul_assoc]
        _ = (u * b) * v := hvub.eq
        _ = u * (b * v) := mul_assoc _ _ _
    have hb1 : b = 1 := by
      by_contra hb1
      exact hvU ⟨hv, hA.centralizer_le_normalizer hb.1 hb1
        (Subgroup.mem_centralizer_singleton_iff.mpr hvb)⟩
    simpa only [hb1, mul_one] using hu
  · intro u hu
    exact ⟨(show V ⊓ Subgroup.normalizer (A : Set G) ≤ _ from le_sup_left) hu,
      Subgroup.mem_centralizer_singleton_iff.mpr
      (show Commute u v from setLike_mul_comm (s := V) hu.1 hv)⟩

private def pair_commutatorMap (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hA : IsTISubgroup A) {v : G} (hv : v ∈ V) :
    ↥(A ⊓ Subgroup.normalizer (V : Set G)) →
      ↥(V ⊓ Subgroup.normalizer (A : Set G)) := fun b =>
  ⟨⁅(b : G), v⁆, by
    rw [← commutatorElement_inv]
    exact (V ⊓ Subgroup.normalizer (A : Set G)).inv_mem
      (ti_pair_commutator_mem_opposite A V hVA.symm hA b.property hv)⟩

private theorem pair_commutatorMap_injective (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hA : IsTISubgroup A) {v : G} (hv : v ∈ V)
    (hvU : v ∉ V ⊓ Subgroup.normalizer (A : Set G)) :
    Function.Injective (pair_commutatorMap V A hVA hA hv) := by
  intro b c heq
  have heq' : ⁅(b : G), v⁆ = ⁅(c : G), v⁆ := congrArg Subtype.val heq
  have hc : Commute ((c : G)⁻¹ * b) v := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      ((c : G)⁻¹ * b) * v * ((c : G)⁻¹ * b)⁻¹ =
        (c : G)⁻¹ * (⁅(b : G), v⁆ * v) * c := by
          simp only [commutatorElement_def]; group
      _ = (c : G)⁻¹ * (⁅(c : G), v⁆ * v) * c := by rw [heq']
      _ = v := by simp only [commutatorElement_def]; group
  have hone : (c : G)⁻¹ * b = 1 := by
    by_contra hne
    exact hvU ⟨hv, hA.centralizer_le_normalizer
      (A.mul_mem (A.inv_mem c.property.1) b.property.1) hne
      (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm)⟩
  exact Subtype.ext ((inv_mul_eq_one.mp hone).symm)

private theorem pair_card_le [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A) :
    Nat.card ↥(A ⊓ Subgroup.normalizer (V : Set G)) ≤
      Nat.card ↥(V ⊓ Subgroup.normalizer (A : Set G)) := by
  by_cases hU : V ⊓ Subgroup.normalizer (A : Set G) = V
  · rw [hU, hcard]
    exact Subgroup.card_le_of_le inf_le_left
  · have hn : ¬ V ≤ V ⊓ Subgroup.normalizer (A : Set G) := by
      intro h
      exact hU (le_antisymm inf_le_left h)
    obtain ⟨v, hv, hvU⟩ := SetLike.not_le_iff_exists.mp hn
    exact Nat.card_le_card_of_injective _
      (pair_commutatorMap_injective V A hVA hA hv hvU)

/-- The mutual normalizers have equal order, including the full-normalizer case. -/
theorem ti_pair_mutual_normalizers_card_eq [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A) :
    Nat.card ↥(V ⊓ Subgroup.normalizer (A : Set G)) =
      Nat.card ↥(A ⊓ Subgroup.normalizer (V : Set G)) := by
  exact le_antisymm (pair_card_le A V hVA.symm hV hcard.symm)
    (pair_card_le V A hVA hA hcard)

/-- Every element of `U` is an individual commutator with `v` of an element
of the embedded opposite factor `B`. -/
theorem ti_pair_exists_commutator [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A) {v : G} (hv : v ∈ V)
    (hvU : v ∉ V ⊓ Subgroup.normalizer (A : Set G))
    {u : G} (hu : u ∈ V ⊓ Subgroup.normalizer (A : Set G)) :
    ∃ b ∈ A ⊓ Subgroup.normalizer (V : Set G), ⁅b, v⁆ = u := by
  have hinj := pair_commutatorMap_injective V A hVA hA hv hvU
  have hsurj := (hinj.bijective_of_nat_card_le
    (ti_pair_mutual_normalizers_card_eq V A hVA hV hA hcard).le).surjective
  obtain ⟨b, hb⟩ := hsurj ⟨u, hu⟩
  exact ⟨b, b.property, congrArg Subtype.val hb⟩

/-- Relative normality is inside `X = V ⊔ A`, not in the ambient group. -/
theorem ti_pair_normal_subgroupOf (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A) :
    (((V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G))).subgroupOf (V ⊔ A)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (ti_pair_sup_le_normalizer V A hVA hV hA)

/-- All commutators of `Y` with `V` lie in the embedded factor `U`. -/
theorem ti_pair_commutator_le_left (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hA : IsTISubgroup A) :
    ⁅(V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G)), V⁆ ≤
        V ⊓ Subgroup.normalizer (A : Set G) := by
  apply Subgroup.commutator_le.mpr
  intro y hy v hv
  obtain ⟨u, hu, b, hb, rfl⟩ := pair_product V A hVA hy
  have hc : ⁅b, v⁆ ∈ V ⊓ Subgroup.normalizer (A : Set G) :=
    (pair_commutatorMap V A hVA hA hv ⟨b, hb⟩).property
  have huv : Commute u v := setLike_mul_comm (s := V) hu.1 hv
  have huc : Commute u ⁅b, v⁆ := setLike_mul_comm (s := V) hu.1 hc.1
  rw [commutatorElement_mul_left_eq_conj_mul, huv.commutator_eq, mul_one,
    huc.eq, mul_inv_cancel_right]
  exact hc

/-- The subgroup commutator `[Y, ⟨v⟩]` is exactly `U` for `v ∈ V − U`.
Both sides are subgroups of the original ambient group, so this equality retains
the prescribed embedding of `U`. -/
theorem ti_pair_commutator_eq [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A) {v : G} (hv : v ∈ V)
    (hvU : v ∉ V ⊓ Subgroup.normalizer (A : Set G)) :
    ⁅(V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G)), Subgroup.zpowers v⁆ =
        V ⊓ Subgroup.normalizer (A : Set G) := by
  apply le_antisymm
  · exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hv)).trans
      (ti_pair_commutator_le_left V A hVA hA)
  · intro u hu
    obtain ⟨b, hb, rfl⟩ := ti_pair_exists_commutator V A hVA hV hA hcard hv hvU hu
    exact Subgroup.commutator_mem_commutator
      ((show A ⊓ Subgroup.normalizer (V : Set G) ≤ _ from le_sup_right) hb)
      (Subgroup.mem_zpowers v)

/-- The symmetric centralizer statement for `a ∈ A − B`, with the same `Y`. -/
theorem ti_pair_centralizer_eq_right (V A : Subgroup G)
    [IsElementaryAbelian 2 A] (hVA : Disjoint V A) (hV : IsTISubgroup V)
    {a : G} (ha : a ∈ A) (haB : a ∉ A ⊓ Subgroup.normalizer (V : Set G)) :
    ((V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G))) ⊓ Subgroup.centralizer ({a} : Set G) =
      A ⊓ Subgroup.normalizer (V : Set G) := by
  simpa only [sup_comm] using ti_pair_centralizer_eq A V hVA.symm hV ha haB

/-- The symmetric commutator statement for `a ∈ A − B`, with the same `Y`. -/
theorem ti_pair_commutator_eq_right [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A) {a : G} (ha : a ∈ A)
    (haB : a ∉ A ⊓ Subgroup.normalizer (V : Set G)) :
    ⁅(V ⊓ Subgroup.normalizer (A : Set G)) ⊔
      (A ⊓ Subgroup.normalizer (V : Set G)), Subgroup.zpowers a⁆ =
        A ⊓ Subgroup.normalizer (V : Set G) := by
  simpa only [sup_comm] using ti_pair_commutator_eq A V hVA.symm hA hV hcard.symm ha haB

end CFSG.Quasithin.ChapterI.Section06To08
