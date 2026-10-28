module

public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo

/-!
# Normalizers along chains of local components

A nonsolvable subgroup lies in at most one C-component: distinct components
intersect in the solvable radical. Apply this inside the join of the larger
local component and S. Conjugation by an element of N_S(L) preserves that
join and the smaller subgroup, hence fixes the containing component.

This proves the first normalizer inclusion in 1.2.8(1) without any model
classification. The reverse inclusion requires the embedding exclusions in
A.3.12 and is not asserted here.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, p.506.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02.Adequate
variable {G : Type*} [Group G] [Finite G]

/-- The first inclusion in the normalizer equality along a local-component chain.
It holds for arbitrary finite groups, independently of the A.3 model list. -/
theorem local_chain_normalizer_le {S B K : Subgroup G}
    (hB : B ∈ L G S) (hK : K ∈ L G S) (hBK : B ≤ K) :
    S ⊓ normalizer (B : Set G) ≤ S ⊓ normalizer (K : Set G) := by
  let J := K ⊔ S
  have hBJ : B ≤ J := hBK.trans le_sup_left
  have hnot : ¬ Group.IsSolvable (B.subgroupOf J) := by
    intro hs
    let := hs
    exact mem_L_not_isSolvable hB
      (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hBJ).toMonoidHom)
        (subgroupOfEquivOfLe hBJ).surjective)
  have hn : ((S ⊓ normalizer (B : Set G)).subgroupOf J) ≤
      normalizer (B.subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hBJ]
    exact comap_mono inf_le_right
  have hk := cComponent_le_normalizer_of_unique hK.1 (comap_mono hBK)
    (fun D hD hBD => IndexTwo.cComponent_unique_over_nonsolvable hnot hD hK.1
      hBD (comap_mono hBK)) hn
  rw [← subgroupOf_normalizer_eq (show K ≤ J from le_sup_left)] at hk
  intro s hs
  exact ⟨hs.1, hk (show (⟨s, (le_sup_right : S ≤ J) hs.1⟩ : J) ∈
    (S ⊓ normalizer (B : Set G)).subgroupOf J from hs)⟩

/-- If S fixes the smaller component in a chain, it fixes the larger one. -/
theorem local_chain_normalizes {S B K : Subgroup G}
    (hB : B ∈ L G S) (hK : K ∈ L G S) (hBK : B ≤ K)
    (hSB : S ≤ normalizer (B : Set G)) : S ≤ normalizer (K : Set G) :=
  (le_inf le_rfl hSB).trans ((local_chain_normalizer_le hB hK hBK).trans inf_le_right)

end CFSG.Quasithin.Chapter1.Section02.Adequate
