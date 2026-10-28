module

public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PGroup.ElementaryNormalizer
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow

/-!
# A central involution from the two-core of a perfect subgroup

Let K be a perfect subgroup normalized by a full Sylow two-subgroup S of
a finite group of two-rank at most two. If O₂(K) is nontrivial, K contains
an involution centralized by both K and S.

The first omega subgroup of the center of O₂(K) supplies a nontrivial
elementary subgroup E invariant under N(K). The rank bound gives |E| ≤ 4,
so perfectness makes K centralize E. As S normalizes E, maximality of S
places E inside S. A nontrivial normal subgroup of the two-group S meets
its center, giving the required involution in E.

This is the core-involution reduction for the odd ternary local section
in Aschbacher–Smith, Proposition 9.3.1, printed pp.732–733. The theorem
uses only the stated finite-group hypotheses and no matrix-group model.
-/

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A perfect subgroup with nontrivial two-core, normalized by a full Sylow
two-subgroup in two-rank at most two, has an involution centralized by their join. -/
public theorem exists_involution_centralized_by_perfect_sup_sylow
    (S : Sylow 2 G) (K : Subgroup G) [Group.IsPerfect K]
    (hr : primeRank 2 G ≤ 2)
    (hSK : (S : Subgroup G) ≤ normalizer (K : Set G))
    (hcore : pCore 2 K ≠ ⊥) :
    ∃ z : G, z ∈ K ∧ orderOf z = 2 ∧
      K ⊔ (S : Subgroup G) ≤ centralizer ({z} : Set G) := by
  let Q := (pCore 2 K).map K.subtype
  have hQtwo : IsPGroup 2 Q := pCore_isPGroup.map K.subtype
  have hQne : Q ≠ ⊥ := by
    intro h
    exact hcore (((pCore 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp h)
  obtain ⟨E, hEne, hEQ, hE, hNE⟩ :=
    exists_nontrivial_elementary_with_normalizer_le Q hQtwo hQne
  let : IsElementaryAbelian 2 E := hE
  have hEK : E ≤ K := hEQ.trans (map_subtype_le _)
  have hNK : normalizer (K : Set G) ≤ normalizer (E : Set G) :=
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K)).trans hNE
  have hKE : K ≤ normalizer (E : Set G) := K.le_normalizer.trans hNK
  have hSE : (S : Subgroup G) ≤ normalizer (E : Set G) := hSK.trans hNK
  have hcard : Nat.card E ≤ 4 :=
    (primeRank_le_iff_elementary_card_le G).mp hr E hE
  let D := E.subgroupOf K
  let : D.Normal := normal_subgroupOf_of_le_normalizer hKE
  have hDcard : Nat.card D ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv]
    exact hcard
  have hKD : (⊤ : Subgroup K) ≤ centralizer (D : Set K) :=
    le_centralizer_of_isPerfect_of_card_le_four _ _ hDcard
  have hES : E ≤ (S : Subgroup G) := by
    have hs := S.is_maximal'
      ((IsElementaryAbelian.isPGroup 2 E).to_sup_of_normal_left' S.isPGroup' hSE)
      (le_sup_right : (S : Subgroup G) ≤ E ⊔ (S : Subgroup G))
    exact (le_sup_left : E ≤ E ⊔ (S : Subgroup G)).trans hs.le
  let R := E.subgroupOf (S : Subgroup G)
  let : R.Normal := normal_subgroupOf_of_le_normalizer hSE
  have hRne : R ≠ ⊥ := by
    intro h
    have hh := congrArg (Subgroup.map (S : Subgroup G).subtype) h
    exact hEne (by simpa only [R, map_subgroupOf_eq_of_le hES, map_bot] using hh)
  have hmeet := center_inf_ne_bot_of_normal S.isPGroup' R hRne
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp hmeet
  have hzE : ((z : S) : G) ∈ E := z.property.2
  have hzK : ((z : S) : G) ∈ K := hEK hzE
  have hz1 : ((z : S) : G) ≠ 1 := by
    intro h
    exact hz (Subtype.ext (Subtype.ext h))
  have hzpow : (((z : S) : G)) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian ((z : S) : G) hzE
  refine ⟨((z : S) : G), hzK, orderOf_eq_prime hzpow hz1, sup_le ?_ ?_⟩
  · intro k hk
    rw [mem_centralizer_singleton_iff]
    exact (congrArg K.subtype
      (hKD (mem_top (⟨k, hk⟩ : K)) ⟨((z : S) : G), hzK⟩ hzE)).symm
  · intro s hs
    rw [mem_centralizer_singleton_iff]
    exact congrArg (S : Subgroup G).subtype
      ((mem_center_iff.mp z.property.1) ⟨s, hs⟩)

end Subgroup
