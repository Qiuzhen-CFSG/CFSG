module

public import Theory.PGroupCore

/-!
# The common normal core of a generating pair

If two subgroups generate a group and their intersection is a Sylow
`p`-subgroup, the `p`-core is the largest subgroup of their intersection
normal in both generators. Normalization by both generators gives ambient
normality, and containment in the Sylow subgroup gives the `p`-group property.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.3 (1 March 2004 manuscript). The argument works for any prime.
-/

namespace Subgroup

variable {G : Type*} [Group G] {p : ℕ}

/-- Normality in two generating subgroups implies ambient normality. -/
public theorem normal_of_normal_in_generating_pair
    (A B N : Subgroup G) (hgen : A ⊔ B = ⊤)
    (hNA : N ≤ A) (hNB : N ≤ B)
    (hA : (N.subgroupOf A).Normal) (hB : (N.subgroupOf B).Normal) :
    N.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  exact sup_le ((normal_subgroupOf_iff_le_normalizer hNA).mp hA)
    ((normal_subgroupOf_iff_le_normalizer hNB).mp hB)

/-- A common normal subgroup of a generating pair contained in a Sylow
intersection lies in the ambient `p`-core. -/
public theorem le_pCore_of_normal_in_generating_pair
    (A B N : Subgroup G) (P : Sylow p G) (hgen : A ⊔ B = ⊤)
    (hP : A ⊓ B = (P : Subgroup G)) (hN : N ≤ A ⊓ B)
    (hA : (N.subgroupOf A).Normal) (hB : (N.subgroupOf B).Normal) :
    N ≤ pCore p G := by
  have hn := normal_of_normal_in_generating_pair A B N hgen
    (hN.trans inf_le_left) (hN.trans inf_le_right) hA hB
  exact le_sSup ⟨hn, P.isPGroup'.to_le (hN.trans hP.le)⟩

/-- The `p`-core is exactly the largest common normal subgroup inside a
Sylow intersection of two generating subgroups. -/
public theorem pCore_isGreatest_common_normal
    (A B : Subgroup G) (P : Sylow p G) (hgen : A ⊔ B = ⊤)
    (hP : A ⊓ B = (P : Subgroup G)) :
    IsGreatest {N : Subgroup G | N ≤ A ⊓ B ∧
      (N.subgroupOf A).Normal ∧ (N.subgroupOf B).Normal} (pCore p G) := by
  refine ⟨⟨?_, inferInstance, inferInstance⟩, ?_⟩
  · rw [hP]
    exact pCore_isPGroup.le_sylow_of_normal P
  · intro N hN
    exact le_pCore_of_normal_in_generating_pair A B N P hgen hP hN.1 hN.2.1 hN.2.2

end Subgroup
