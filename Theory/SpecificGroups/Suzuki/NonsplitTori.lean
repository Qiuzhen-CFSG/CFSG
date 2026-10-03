module

public import Theory.SpecificGroups.Suzuki.NonsplitPartitionCounting
public import Theory.SpecificGroups.Suzuki.NonsplitNormalizerComplements
public import Theory.SpecificGroups.Suzuki.NonsplitTorusArithmetic

/-!
# The two nonsplit tori of a Suzuki group

The subgroup partition count forces exactly two nonsplit conjugacy classes,
both with normalizer quotient of order four. Their orders have product `q²+1`
and sum `2(q+1)`, so are `q+2r+1` and `q-2r+1`, where `r=2^m`.
We assemble concrete cyclic Hall representatives, their centralizers, the
partition, and cyclic normalizer complements acting by right conjugation
as the `q`th power map.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.10(i)--(j),
printed pp. 192--193.
-/

namespace BenderSuzuki.MatrixGroups

open scoped Classical

/-- The partition count determines two representatives, their normalizer
indices, and the sum and product of their orders. -/
public theorem SuzukiNonsplitRepresentatives.two_classes {m : ℕ} (hm : 0 < m)
    (R : SuzukiNonsplitRepresentatives m) :
    ∃ U V : Subgroup (SuzukiMatrixGroup m), U ≠ V ∧ R.subgroups = {U, V} ∧
      U.relIndex (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) = 4 ∧
      V.relIndex (Subgroup.normalizer (V : Set (SuzukiMatrixGroup m))) = 4 ∧
      Nat.card U * Nat.card V = (2 ^ (2 * m + 1)) ^ 2 + 1 ∧
      Nat.card U + Nat.card V = 2 * (2 ^ (2 * m + 1) + 1) := by
  classical
  apply suzuki_nonsplit_counting_arithmetic R.subgroups
    (fun U => Nat.card U)
    (fun U => U.relIndex (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))))
  · exact (show 8 = (2 : ℕ) ^ 3 by norm_num).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  · intro U hU
    apply suzuki_nonsplit_divisor_lower_bound m (Nat.card U) _ (R.maximal U hU).card_dvd
    have hpos : 0 < Nat.card U := Nat.card_pos
    have hne : Nat.card U ≠ 1 := fun h =>
      (R.maximal U hU).ne_bot hm (Subgroup.card_eq_one.mp h)
    omega
  · exact fun U hU => (R.maximal U hU).normalizer_index hm
  · exact R.prod_card hm
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using R.normalized_counting_identity hm

/-- Every transversal of the nonsplit conjugacy classes has cardinality two. -/
public theorem SuzukiNonsplitRepresentatives.card_eq_two {m : ℕ} (hm : 0 < m)
    (R : SuzukiNonsplitRepresentatives m) : R.subgroups.card = 2 := by
  classical
  obtain ⟨U, V, hne, hR, _⟩ := R.two_classes hm
  simp [hR, hne]

/-- Representatives can be ordered by the two explicit torus orders. -/
public theorem SuzukiNonsplitRepresentatives.exact_orders {m : ℕ} (hm : 0 < m)
    (R : SuzukiNonsplitRepresentatives m) :
    ∃ U V : Subgroup (SuzukiMatrixGroup m), U ≠ V ∧ R.subgroups = {U, V} ∧
      Nat.card U = 2 ^ (2 * m + 1) + 2 * 2 ^ m + 1 ∧
      Nat.card V = 2 ^ (2 * m + 1) - 2 * 2 ^ m + 1 ∧
      U.relIndex (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) = 4 ∧
      V.relIndex (Subgroup.normalizer (V : Set (SuzukiMatrixGroup m))) = 4 := by
  classical
  obtain ⟨U, V, hne, hR, hU, hV, hmul, hsum⟩ := R.two_classes hm
  rcases suzuki_nonsplit_orders_of_sum_mul m (Nat.card U) (Nat.card V) hmul hsum
    with h | h
  · exact ⟨U, V, hne, hR, h.1, h.2, hU, hV⟩
  · exact ⟨V, U, hne.symm, hR.trans (Finset.pair_comm U V), h.1, h.2, hV, hU⟩


/-- Every maximal nonsplit torus has normalizer index four. -/
public theorem IsSuzukiMaximalNonsplit.normalizer_index_eq_four {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalNonsplit m U) :
    U.relIndex (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) = 4 := by
  obtain ⟨R⟩ := exists_suzukiNonsplitRepresentatives m hm
  obtain ⟨A, B, _, hR, hA, hB, _⟩ := R.two_classes hm
  obtain ⟨V, hV, g, rfl⟩ := R.covers U hU
  rw [← Subgroup.map_normalizer_eq_of_bijective V (MulAut.conj g).bijective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  have hV' : V = A ∨ V = B := by simpa [hR] using hV
  rcases hV' with rfl | rfl
  · exact hA
  · exact hB

/-- The normalizer quotient of every maximal nonsplit torus is cyclic of
order four. -/
public theorem IsSuzukiMaximalNonsplit.normalizer_quotient_order_four
    {m : ℕ} (hm : 0 < m) {U : Subgroup (SuzukiMatrixGroup m)}
    (hU : IsSuzukiMaximalNonsplit m U) :
    IsCyclic ((Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) ⧸
      U.subgroupOf (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)))) ∧
    Nat.card ((Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) ⧸
      U.subgroupOf (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)))) = 4 :=
  ⟨(hU.normalizer_quotient hm).1, hU.normalizer_index_eq_four hm⟩

/-- The normalizer splits over a cyclic complement of order four whose
chosen generator acts by `t⁻¹ * u * t = u^q`. -/
public theorem IsSuzukiMaximalNonsplit.normalizer_complement {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalNonsplit m U) :
    ∃ t : SuzukiMatrixGroup m,
      orderOf t = 4 ∧
      t ∈ Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)) ∧
      U ⊔ Subgroup.zpowers t = Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)) ∧
      Disjoint U (Subgroup.zpowers t) ∧
      ∀ u ∈ U, t⁻¹ * u * t = u ^ (2 ^ (2 * m + 1)) :=
  hU.exists_order_four_complement hm (hU.normalizer_index_eq_four hm)

/-- An ordered concrete pair representing the two nonsplit conjugacy classes.
The plus torus has the larger order. -/
public structure SuzukiNonsplitTorusPair (m : ℕ) where
  plus : Subgroup (SuzukiMatrixGroup m)
  minus : Subgroup (SuzukiMatrixGroup m)
  plus_maximal : IsSuzukiMaximalNonsplit m plus
  minus_maximal : IsSuzukiMaximalNonsplit m minus
  plus_card : Nat.card plus = 2 ^ (2 * m + 1) + 2 * 2 ^ m + 1
  minus_card : Nat.card minus = 2 ^ (2 * m + 1) - 2 * 2 ^ m + 1
  not_conjugate : ¬ ∃ g : SuzukiMatrixGroup m,
    minus = plus.map (MulAut.conj g).toMonoidHom
  covers : ∀ U, IsSuzukiMaximalNonsplit m U →
    (∃ g, U = plus.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, U = minus.map (MulAut.conj g).toMonoidHom)

/-- There exists an ordered pair of concrete nonsplit tori with the exact
orders, representing precisely the two conjugacy classes. -/
public theorem exists_suzukiNonsplitTorusPair (m : ℕ) (hm : 0 < m) :
    Nonempty (SuzukiNonsplitTorusPair m) := by
  obtain ⟨R⟩ := exists_suzukiNonsplitRepresentatives m hm
  obtain ⟨U, V, hne, hR, hU, hV, _⟩ := R.exact_orders hm
  have hUR : U ∈ R.subgroups := by simp [hR]
  have hVR : V ∈ R.subgroups := by simp [hR]
  refine ⟨⟨U, V, R.maximal U hUR, R.maximal V hVR, hU, hV,
    R.not_conjugate U hUR V hVR hne, ?_⟩⟩
  intro W hW
  obtain ⟨A, hA, g, hg⟩ := R.covers W hW
  have : A = U ∨ A = V := by simpa [hR] using hA
  rcases this with rfl | rfl
  · exact Or.inl ⟨g, hg⟩
  · exact Or.inr ⟨g, hg⟩

/-- Both concrete representatives are cyclic Hall subgroups. -/
public theorem SuzukiNonsplitTorusPair.cyclic_hall {m : ℕ} (hm : 0 < m)
    (T : SuzukiNonsplitTorusPair m) :
    IsCyclic T.plus ∧ Nat.Coprime (Nat.card T.plus) T.plus.index ∧
    IsCyclic T.minus ∧ Nat.Coprime (Nat.card T.minus) T.minus.index :=
  ⟨T.plus_maximal.isCyclic hm, T.plus_maximal.card_coprime_index hm,
    T.minus_maximal.isCyclic hm, T.minus_maximal.card_coprime_index hm⟩

/-- Nonidentity elements of either torus have that torus as centralizer. -/
public theorem SuzukiNonsplitTorusPair.centralizers {m : ℕ} (hm : 0 < m)
    (T : SuzukiNonsplitTorusPair m) :
    (∀ u ∈ T.plus, u ≠ 1 → Subgroup.centralizer {u} = T.plus) ∧
    (∀ u ∈ T.minus, u ≠ 1 → Subgroup.centralizer {u} = T.minus) :=
  ⟨fun _ hu hne => T.plus_maximal.centralizer_eq hm hu hne,
    fun _ hu hne => T.minus_maximal.centralizer_eq hm hu hne⟩

/-- The subgroup partition uses just the root group, the split torus, and
the two concrete nonsplit tori. Membership is unique away from the identity. -/
public theorem SuzukiNonsplitTorusPair.partition_existsUnique {m : ℕ} (hm : 0 < m)
    (T : SuzukiNonsplitTorusPair m) (x : SuzukiMatrixGroup m) (hx : x ≠ 1) :
    ∃! U : Subgroup (SuzukiMatrixGroup m),
      ((∃ g, U = (SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, U = (SuzukiSplitTorus m).map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, U = T.plus.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, U = T.minus.map (MulAut.conj g).toMonoidHom)) ∧ x ∈ U := by
  obtain ⟨R⟩ := exists_suzukiNonsplitRepresentatives m hm
  have hiff (U : Subgroup (SuzukiMatrixGroup m)) :
      (∃ V ∈ R.subgroups, ∃ g, U = V.map (MulAut.conj g).toMonoidHom) ↔
        (∃ g, U = T.plus.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, U = T.minus.map (MulAut.conj g).toMonoidHom) := by
    constructor
    · rintro ⟨V, hV, g, rfl⟩
      exact T.covers _ ((R.maximal V hV).map_conj g)
    · rintro (⟨g, rfl⟩ | ⟨g, rfl⟩)
      · exact R.covers _ (T.plus_maximal.map_conj g)
      · exact R.covers _ (T.minus_maximal.map_conj g)
  simpa only [hiff] using R.partition_existsUnique hm x hx

end BenderSuzuki.MatrixGroups
