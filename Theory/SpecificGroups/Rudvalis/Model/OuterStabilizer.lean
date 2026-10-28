module

public import Theory.SpecificGroups.Rudvalis.Model.Primitive
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.OrbitCounting
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding
public import Theory.SpecificGroups.Tits.Atlas1600Order
public import Theory.SpecificGroups.Tits.MinimumIndex
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# A Tits-subgroup route to Rudvalis stabilizer-class invariance

Write H for the stabilizer of 0 in the actual degree-4060 model. Suppose
K ≤ H has index two, Tits order, and no proper subgroup of index below 1600.
For any automorphism f of the model, orbit counting forces f(K) to fix some
point y. The point stabilizer J at y and f(H) have the same index, so f(K)
has index two in both. It is therefore normal in both. Simplicity and the
maximality of J force its normalizer to equal J, giving f(H) = J.

The final theorem uses the actual multiplicative equivalence from the
checked degree-1600 Tits carrier to the index-two subgroup constructed in
`TitsEmbedding`, transporting its order and the bound proved in
`Tits.MinimumIndex`. Thus `Rudvalis.outer_stabilizer_map_eq` retains only
simplicity of the Rudvalis model as a hypothesis.

Source motivation: GLS3, Table 5.3r, printed p.279
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`), describes the coset action of Ru
on the full group ²F₄(2). Its stabilizer has an index-two simple Tits subgroup;
the full stabilizer is not the simple group of order 17971200.
The quasithin consumer is on printed pp.33 and 510 of `refs/quasithin.pdf`.
This proof is independent of the permutation-normalizer and outer-group
calculations.
-/

namespace Rudvalis
open MulAction

/-- Two equal-index subgroups of a finite simple group coincide if one is
maximal and they contain a common nontrivial subgroup of index two. -/
private theorem eq_of_common_index_two_subgroup {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H J K : Subgroup G) (hJ : IsCoatom J) (hKH : K ≤ H) (hKJ : K ≤ J)
    (hi : H.index = J.index) (htwo : K.relIndex H = 2) (hne : K ≠ ⊥) : H = J := by
  have htwoJ : K.relIndex J = 2 := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := J)))
    calc
      K.relIndex J * J.index = K.index := Subgroup.relIndex_mul_index hKJ
      _ = K.relIndex H * H.index := (Subgroup.relIndex_mul_index hKH).symm
      _ = 2 * J.index := by rw [htwo, hi]
  have hnormH : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp
      (Subgroup.normal_of_index_eq_two htwo)
  have hnormJ : J ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mp
      (Subgroup.normal_of_index_eq_two htwoJ)
  have hn : Subgroup.normalizer (K : Set G) ≠ ⊤ := by
    intro he
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K
      (Subgroup.normalizer_eq_top_iff.mp he) with he | he
    · exact hne he
    · exact hJ.1 (top_le_iff.mp (he ▸ hKJ))
  have hnJ : Subgroup.normalizer (K : Set G) = J := (hJ.le_iff_eq hn).mp hnormJ
  have hHJ : H ≤ J := hnJ ▸ hnormH
  apply le_antisymm hHJ
  apply Subgroup.relIndex_eq_one.mp
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := J)))
  simpa only [one_mul, hi] using Subgroup.relIndex_mul_index hHJ


/-- Conditional stabilizer-class invariance from an index-two subgroup with
the Tits order and minimum-index bound. All subgroup indices are relative
to the displayed overgroup. -/
public theorem outer_stabilizer_map_eq_of_index_two [IsSimpleGroup Model]
    (K : Subgroup Model)
    (hK : K ≤ stabilizer Model (0 : Fin 4060))
    (hindex : K.relIndex (stabilizer Model (0 : Fin 4060)) = 2)
    (hcard : Nat.card K = 17971200)
    (hmin : ∀ L : Subgroup K, L ≠ ⊤ → 1600 ≤ L.index)
    (f : MulAut Model) : ∃ y : Fin 4060,
      (stabilizer Model (0 : Fin 4060)).map f.toMonoidHom = stabilizer Model y := by
  let : MulAction K (Fin 4060) :=
    MulAction.compHom (Fin 4060) (f.toMonoidHom.comp K.subtype)
  obtain ⟨y, hy⟩ := OuterStabilizer.exists_fixed_point_of_order_of_min_index (K := K) hcard hmin
    (by simp : Nat.card (Fin 4060) = 4060)
  have hKy : K.map f.toMonoidHom ≤ stabilizer Model y := by
    rintro _ ⟨k, hk, rfl⟩
    exact hy ⟨k, hk⟩
  let := model_isPreprimitive
  let := model_isPretransitive
  refine ⟨y, eq_of_common_index_two_subgroup _ _ _
    (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive Model y)
    (Subgroup.map_mono hK) hKy ?_ ?_ ?_⟩
  · rw [Subgroup.index_map_of_bijective (f := f.toMonoidHom) f.bijective,
      index_stabilizer_of_transitive,
      index_stabilizer_of_transitive]
  · exact (Subgroup.relIndex_map_map_of_injective _ _ f.injective).trans hindex
  · intro hbot
    have hc : Nat.card (K.map f.toMonoidHom) = 17971200 :=
      (Subgroup.card_map_of_injective f.injective).trans hcard
    rw [hbot, Subgroup.card_bot] at hc
    contradiction


/-- A concrete Tits embedding and the Tits minimum-index bound suffice for
the Rudvalis point-stabilizer class to be invariant under every automorphism. -/
public theorem outer_stabilizer_map_eq_of_tits_subgroup [IsSimpleGroup Model]
    (hmin : ∀ L : Subgroup Tits.Atlas1600Group, L ≠ ⊤ → 1600 ≤ L.index)
    (K : Subgroup Model) (e : Tits.Atlas1600Group ≃* K)
    (hK : K ≤ stabilizer Model (0 : Fin 4060))
    (hindex : K.relIndex (stabilizer Model (0 : Fin 4060)) = 2)
    (f : MulAut Model) : ∃ y : Fin 4060,
      (stabilizer Model (0 : Fin 4060)).map f.toMonoidHom = stabilizer Model y := by
  apply outer_stabilizer_map_eq_of_index_two K hK hindex
  · exact (Nat.card_congr e.toEquiv).symm.trans Tits.atlas1600Group_card
  · intro L hL
    have hproper : L.comap e.toMonoidHom ≠ ⊤ := by
      intro he
      apply hL
      apply top_le_iff.mp
      intro k _
      obtain ⟨t, rfl⟩ := e.surjective k
      exact show t ∈ L.comap e.toMonoidHom from he ▸ Subgroup.mem_top t
    have ht := hmin _ hproper
    rwa [L.index_comap_of_surjective e.surjective] at ht

/-- Every automorphism of the concrete Rudvalis model carries the stabilizer
of 0 to a point stabilizer in its degree-4060 action. The actual index-two
Tits embedding and its minimum proper-subgroup index discharge all inputs
of the stabilizer-class reduction. -/
public theorem outer_stabilizer_map_eq [IsSimpleGroup Model]
    (f : MulAut Model) : ∃ y : Fin 4060,
      (stabilizer Model (0 : Fin 4060)).map f.toMonoidHom = stabilizer Model y := by
  obtain ⟨K, hK, hindex, ⟨e⟩⟩ := outer_stabilizer_tits_subgroup
  exact outer_stabilizer_map_eq_of_tits_subgroup
    Tits.atlas1600_subgroup_index_ge K e hK hindex f

end Rudvalis
