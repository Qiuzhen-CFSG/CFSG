module
public import Theory.GroupTheory.ElementaryCommutingNormalFour
public import Theory.GroupTheory.PGroup.NormalElementaryFour

/-!
# Rank-three commuting paths in finite two-groups

If a subgroup S contains a normal elementary four-group E, any two
elementary binary subgroups of S of order at least eight are connected
in the actual elementary commuting relation of the ambient group.
Each is connected to E through the kernel of its conjugation action.

In a finite two-group the required normal four-group exists as soon as
one rank-three elementary subgroup does, by GLS2, Lemma 10.11. Thus all
rank-three elementary subgroups of a finite two-group are connected,
both internally and as subgroups of any finite ambient group. The path
argument is the relevant part of Lemmas 10.20 and 10.21
(`refs/KGroup/GLS2/ChapterC.tex`).
-/

namespace Subgroup

/-- Rank-three elementary subgroups normalizing the same four-group
belong to the same commuting component. -/
public theorem elementaryCommutingConnected_of_common_normalized_four
    {G : Type*} [Group G] [Finite G]
    (A B E : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) (hE : Nat.card E = 4)
    (hAE : A ≤ normalizer (E : Set G)) (hBE : B ≤ normalizer (E : Set G)) :
    ElementaryCommutingConnected 2 A B :=
  (elementaryCommutingConnected_of_normalizes_four A E hA hE hAE).trans
    (elementaryCommutingConnected_of_normalizes_four B E hB hE hBE).symm

/-- A normal four-group in S connects all rank-three elementary
subgroups of S, viewed as subgroups of the ambient group. -/
public theorem elementaryCommutingConnected_of_le_of_normal_four
    {G : Type*} [Group G] [Finite G]
    (S A B : Subgroup G) (E : Subgroup S) [E.Normal]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) (hE : Nat.card E = 4)
    (hAS : A ≤ S) (hBS : B ≤ S) : ElementaryCommutingConnected 2 A B := by
  let _ : IsElementaryAbelian 2 (E.map S.subtype) := IsElementaryAbelian.map_subtype
  have hSE : S ≤ normalizer (E.map S.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using E.le_normalizer_map S.subtype
  exact elementaryCommutingConnected_of_common_normalized_four A B (E.map S.subtype)
    hA hB (by simpa only [card_map_of_injective S.subtype_injective] using hE)
    (hAS.trans hSE) (hBS.trans hSE)

/-- All rank-three elementary subgroups of a finite two-group belong to
the same elementary commuting component. -/
public theorem elementaryCommutingConnected_of_twoGroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A B : Subgroup P) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) :
    ElementaryCommutingConnected 2 A B := by
  obtain ⟨E, hEn, hEe, hE⟩ := hP.exists_normal_elementaryAbelian_four A hA
  let _ : E.Normal := hEn
  let _ : IsElementaryAbelian 2 E := hEe
  exact elementaryCommutingConnected_of_common_normalized_four A B E hA hB hE
    (by simp only [normalizer_eq_top, le_top])
    (by simp only [normalizer_eq_top, le_top])

/-- Rank-three elementary subgroups contained in a common finite
two-subgroup are connected in the ambient elementary commuting relation. -/
public theorem elementaryCommutingConnected_of_le_twoGroup
    {G : Type*} [Group G] [Finite G]
    (S A B : Subgroup G) (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) (hAS : A ≤ S) (hBS : B ≤ S) :
    ElementaryCommutingConnected 2 A B := by
  let _ : IsElementaryAbelian 2 (A.subgroupOf S) := IsElementaryAbelian.subgroupOf hAS
  have hAScard : 8 ≤ Nat.card (A.subgroupOf S) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv]
  obtain ⟨E, hEn, hEe, hE⟩ :=
    hS.exists_normal_elementaryAbelian_four (A.subgroupOf S) hAScard
  let _ : E.Normal := hEn
  let _ : IsElementaryAbelian 2 E := hEe
  exact elementaryCommutingConnected_of_le_of_normal_four S A B E hA hB hE hAS hBS

end Subgroup
