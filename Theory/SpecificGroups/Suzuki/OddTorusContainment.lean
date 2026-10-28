module

public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import Theory.SpecificGroups.Suzuki.NonsplitTori
public import Theory.SpecificGroups.Suzuki.AbelianSubgroups
public import Theory.GroupTheory.SolvableNormalAbelian
public import Theory.GroupTheory.OddInvolutionNormalizer
import Mathlib.GroupTheory.FixedPointFree

/-!
# Odd subgroups and involutions in the concrete Suzuki group

Every odd-order subgroup of `SuzukiMatrixGroup m`, for `m > 0`, lies in a
cyclic maximal torus of order `q - 1`, `q + 2^(m+1) + 1`, or
`q - 2^(m+1) + 1`, where `q = 2^(2m+1)`. Every involution normalizing such
a torus inverts it. The small-normalizer hypothesis `N(H) ≤ H ⊔ ⟨t⟩`
therefore forces `H` to be a full torus and gives `|H : C_H(t)| = |H|`.

For containment, odd-order subgroups are already known to be solvable.
Choose a nontrivial abelian normal subgroup and its unique root/torus
partition member. Oddness excludes a root member; partition uniqueness
puts the whole subgroup in the torus normalizer. Its index two or four
then puts the odd subgroup in the torus. This refines the normal-abelian
argument for solvable standard containment without needing a separate
Borel complement-conjugacy theorem. For inversion, a normalizing involution
has no nonidentity fixed point in the torus: the partition centralizer
bound would otherwise put the involution in that odd-order torus.

Sources: GLS, Volume 4, Chapter 4, the odd-order clause of Lemma 3.8,
and Chapter 2, the Suzuki model input to Lemma 17.3. The torus orders use
GLS, Volume 3, Theorem 6.5.4 (`refs/KGroup/GLS3/chapter6.tex`), correcting
the garbled square-root notation in the Volume 4 transcription.
-/

namespace BenderSuzuki.MatrixGroups

/-- A conjugate of the split torus or a maximal nonsplit torus. -/
@[expose] public def IsSuzukiMaximalOddTorus (m : ℕ) (U : Subgroup (SuzukiMatrixGroup m)) : Prop :=
  (∃ g, U = (SuzukiSplitTorus m).map (MulAut.conj g).toMonoidHom) ∨
    IsSuzukiMaximalNonsplit m U

/-- The odd maximal tori are members of the concrete root/torus partition. -/
public theorem IsSuzukiMaximalOddTorus.partition {m : ℕ}
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalOddTorus m U) :
    SuzukiPartitionMember m U :=
  (suzukiPartitionMember_iff m U).mpr (Or.inr hU)

/-- Every maximal odd torus is cyclic. -/
public theorem IsSuzukiMaximalOddTorus.isCyclic {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalOddTorus m U) :
    IsCyclic U := by
  rcases hU with ⟨g, rfl⟩ | hU
  · let := suzukiSplitTorus_isCyclic m hm
    exact ((SuzukiSplitTorus m).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).isCyclic.mp inferInstance
  · exact hU.isCyclic hm

/-- The split and both nonsplit tori have odd order. -/
public theorem IsSuzukiMaximalOddTorus.odd_card {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalOddTorus m U) :
    Odd (Nat.card U) := by
  have he : Even ((2 : ℕ) ^ (2 * m + 1)) :=
    even_two.pow_of_ne_zero (by omega)
  rcases hU with ⟨g, rfl⟩ | hU
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      suzukiSplitTorus_card m hm]
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide)) he odd_one
  · exact Odd.of_dvd_nat ((he.pow_of_ne_zero (by decide : 2 ≠ 0)).add_one) hU.card_dvd

/-- The exact three torus orders, with q = 2^(2m+1). -/
public theorem IsSuzukiMaximalOddTorus.card_eq {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalOddTorus m U) :
    Nat.card U = 2 ^ (2 * m + 1) - 1 ∨
    Nat.card U = 2 ^ (2 * m + 1) + 2 ^ (m + 1) + 1 ∨
    Nat.card U = 2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1 := by
  rcases hU with ⟨g, rfl⟩ | hU
  · exact Or.inl (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      suzukiSplitTorus_card m hm])
  · obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair m hm
    rcases T.covers U hU with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact Or.inr (Or.inl (by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, T.plus_card]
        simp only [pow_succ, Nat.mul_comm]))
    · exact Or.inr (Or.inr (by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, T.minus_card]
        simp only [pow_succ, Nat.mul_comm]))

private theorem split_normalizer_index {m : ℕ} (hm : 0 < m) :
    (SuzukiSplitTorus m).relIndex (Subgroup.normalizer (SuzukiSplitTorus m)) = 2 := by
  let N := Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))
  let A := (SuzukiSplitTorus m).subgroupOf N
  have hc : Nat.card A = Nat.card (SuzukiSplitTorus m) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have h := A.card_mul_index
  rw [hc, suzukiSplitTorus_card m hm, suzukiSplitTorus_normalizer_card m hm] at h
  change A.index = 2
  have hp : 0 < Nat.card (SuzukiSplitTorus m) := Nat.card_pos
  rw [suzukiSplitTorus_card m hm] at hp
  nlinarith

/-- The torus has index two or four in its normalizer. -/
public theorem IsSuzukiMaximalOddTorus.normalizer_index {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalOddTorus m U) :
    U.relIndex (Subgroup.normalizer U) = 2 ∨
    U.relIndex (Subgroup.normalizer U) = 4 := by
  rcases hU with ⟨g, rfl⟩ | hU
  · left
    rw [← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact split_normalizer_index hm
  · exact Or.inr (hU.normalizer_index_eq_four hm)

private theorem odd_le_of_normalizer_index {G : Type*} [Group G] [Finite G]
    (H U : Subgroup G) (hodd : Odd (Nat.card H))
    (hHU : H ≤ Subgroup.normalizer U)
    (hindex : U.relIndex (Subgroup.normalizer U) = 2 ∨
      U.relIndex (Subgroup.normalizer U) = 4) : H ≤ U := by
  let N := Subgroup.normalizer (U : Set G)
  let A := U.subgroupOf N
  let B := H.subgroupOf N
  let : A.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hB : Nat.card B = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHU).toEquiv
  have hoddB : Odd (Nat.card B) := hB ▸ hodd
  have hd : A.relIndex B ∣ A.index := Subgroup.relIndex_dvd_index_of_normal A B
  have hi : A.relIndex B = 1 := by
    rcases hindex with hi | hi
    · change A.index = 2 at hi
      rw [hi] at hd
      exact Nat.eq_one_of_dvd_coprimes hoddB.coprime_two_right
        (A.relIndex_dvd_card B) hd
    · change A.index = 4 at hi
      rw [hi] at hd
      exact Nat.eq_one_of_dvd_coprimes (hoddB.coprime_two_right.pow_right 2)
        (A.relIndex_dvd_card B) hd
  have hBA : B ≤ A := Subgroup.relIndex_eq_one.mp hi
  exact fun x hx => hBA (show (⟨x, hHU hx⟩ : N) ∈ B from hx)

/-- An odd-order subgroup of a torus normalizer lies in the torus itself. -/
public theorem IsSuzukiMaximalOddTorus.odd_subgroup_le {m : ℕ} (hm : 0 < m)
    {U H : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalOddTorus m U)
    (hodd : Odd (Nat.card H)) (hH : H ≤ Subgroup.normalizer U) : H ≤ U :=
  odd_le_of_normalizer_index H U hodd hH (hU.normalizer_index hm)

/-- Every odd-order subgroup lies in an actual maximal torus. -/
public theorem suzukiOddSubgroup_exists_torus {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hodd : Odd (Nat.card H)) :
    ∃ U, H ≤ U ∧ IsSuzukiMaximalOddTorus m U := by
  by_cases hH : H = ⊥
  · refine ⟨SuzukiSplitTorus m, hH ▸ bot_le, Or.inl ⟨1, ?_⟩⟩
    ext x
    simp
  let : Group.IsSolvable H := suzukiSubgroup_isSolvable_of_odd hm H hodd
  let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  obtain ⟨A, hAn, hAc, hA⟩ := Group.exists_nontrivial_abelian_normal H
  let : A.Normal := hAn
  let : IsMulCommutative A := hAc
  let B := A.map H.subtype
  have hB : B ≠ ⊥ := by
    intro hB
    apply hA
    exact (A.map_eq_bot_iff_of_injective H.subtype_injective).mp hB
  have hBH : B ≤ H := Subgroup.map_subtype_le A
  obtain ⟨U, ⟨hU, hBU⟩, _⟩ := suzukiAbelianSubgroup_partition_existsUnique hm B hB
  have hHN : H ≤ Subgroup.normalizer B := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh b hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨(⟨h, hh⟩ : H) * a * (⟨h, hh⟩ : H)⁻¹,
      hAn.conj_mem a ha ⟨h, hh⟩, rfl⟩
  have htor : IsSuzukiMaximalOddTorus m U := by
    rcases (suzukiPartitionMember_iff m U).mp hU with ⟨g, rfl⟩ | htor
    · exfalso
      have hcop : Nat.Coprime (Nat.card H)
          (Nat.card ((SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom)) := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
          suzukiRootSubgroup_card m hm]
        exact (hodd.coprime_two_right.pow_right _).pow_right _
      have hd := Subgroup.disjoint_of_coprime_natCard hcop
      exact hB (le_antisymm ((le_inf hBH hBU).trans hd.le_bot) bot_le)
    · exact htor
  exact ⟨U, htor.odd_subgroup_le hm hodd
    (hHN.trans (hU.normalizer_le hm hBU hB)), htor⟩

/-- Odd-order Suzuki subgroups are cyclic, hence abelian. -/
public theorem suzukiOddSubgroup_isCyclic {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hodd : Odd (Nat.card H)) : IsCyclic H := by
  obtain ⟨U, hHU, hU⟩ := suzukiOddSubgroup_exists_torus hm H hodd
  let := hU.isCyclic hm
  exact Subgroup.isCyclic_of_le hHU

/-- An involution normalizing a torus acts by inversion on it. -/
public theorem IsSuzukiMaximalOddTorus.involution_inverts {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalOddTorus m U)
    {t : SuzukiMatrixGroup m} (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer U) :
    ∀ x ∈ U, t * x * t⁻¹ = x⁻¹ := by
  let α : MulAut U := U.normalizerMonoidHom ⟨t, htN⟩
  have htU : t ∉ U := by
    intro h
    have hd := U.orderOf_dvd_natCard h
    rw [ht] at hd
    exact (hU.odd_card hm).not_two_dvd_nat hd
  have hfree : MonoidHom.FixedPointFree α := by
    intro x hx
    by_contra hne
    have hxne : (x : SuzukiMatrixGroup m) ≠ 1 := fun h => hne (Subtype.ext h)
    have he : t * (x : SuzukiMatrixGroup m) * t⁻¹ = x := congrArg Subtype.val hx
    have hc : t ∈ Subgroup.centralizer {(x : SuzukiMatrixGroup m)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp he)
    exact htU (hU.partition.centralizer_le hm x.property hxne hc)
  have htwo : Function.Involutive α := by
    intro x
    apply Subtype.ext
    change t * (t * (x : SuzukiMatrixGroup m) * t⁻¹) * t⁻¹ = x
    have htt : t * t = 1 := by simpa only [← pow_two, ← ht] using pow_orderOf_eq_one t
    calc
      _ = (t * t) * (x : SuzukiMatrixGroup m) * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; simp
  intro x hx
  exact congrArg Subtype.val (congrFun (hfree.coe_eq_inv_of_involutive htwo) ⟨x, hx⟩)

/-- The source's torus containment, including the exact orders and involution action. -/
public theorem suzukiOddSubgroup_torus_containment {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hodd : Odd (Nat.card H)) :
    ∃ U : Subgroup (SuzukiMatrixGroup m), H ≤ U ∧ IsCyclic U ∧
      (Nat.card U = 2 ^ (2 * m + 1) - 1 ∨
       Nat.card U = 2 ^ (2 * m + 1) + 2 ^ (m + 1) + 1 ∨
       Nat.card U = 2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1) ∧
      ∀ t : SuzukiMatrixGroup m, orderOf t = 2 → t ∈ Subgroup.normalizer U →
        ∀ x ∈ U, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨U, hHU, hU⟩ := suzukiOddSubgroup_exists_torus hm H hodd
  exact ⟨U, hHU, hU.isCyclic hm, hU.card_eq hm,
    fun _ ht htN => hU.involution_inverts hm ht htN⟩

/-- The small-normalizer hypothesis exhausts the containing torus. -/
public theorem suzukiOddSubgroup_eq_torus_of_normalizer_le {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hodd : Odd (Nat.card H))
    {t : SuzukiMatrixGroup m} (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer H)
    (hN : Subgroup.normalizer H ≤ H ⊔ Subgroup.zpowers t) :
    IsSuzukiMaximalOddTorus m H := by
  obtain ⟨U, hHU, hU⟩ := suzukiOddSubgroup_exists_torus hm H hodd
  let := hU.isCyclic hm
  have he := H.eq_odd_abelian_overgroup_of_normalizer_le U hHU (hU.odd_card hm) ht htN hN
  exact he ▸ hU

/-- The centralizer index in the odd subgroup is its full torus order. -/
public theorem suzukiOddSubgroup_centralizer_index {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hodd : Odd (Nat.card H))
    {t : SuzukiMatrixGroup m} (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer H)
    (hN : Subgroup.normalizer H ≤ H ⊔ Subgroup.zpowers t) :
    (Subgroup.centralizer ({t} : Set (SuzukiMatrixGroup m))).relIndex H = Nat.card H ∧
      (Nat.card H = 2 ^ (2 * m + 1) - 1 ∨
       Nat.card H = 2 ^ (2 * m + 1) + 2 ^ (m + 1) + 1 ∨
       Nat.card H = 2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1) := by
  have hH := suzukiOddSubgroup_eq_torus_of_normalizer_le hm H hodd ht htN hN
  exact ⟨H.centralizer_relIndex_eq_card_of_odd_inverted hodd t
    (hH.involution_inverts hm ht htN), hH.card_eq hm⟩

end BenderSuzuki.MatrixGroups
