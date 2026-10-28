module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.CubicComparison
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Restricting the original normalized cubic to the normal closure

The inversion identity puts the original cubic generator in the literal normal
closure of the distinguished involution. Intersecting the original full Sylow
subgroup with that normal closure gives an actual intrinsic Sylow which still
normalizes the same cubic. Consequently the binary linear actor sieve applies
to any actual model of the normal closure, independently of its module marking.

Source: Aschbacher–Smith, C.5.12, p.163, through the G.6.4 argument, pp.345–346.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section06
variable {G : Type*} [Group G]

theorem inverted_element_mem_normalClosure (a c : G) (hi : a * c = c ^ 2 * a) :
    c ∈ normalClosure ({a} : Set G) := by
  let K := normalClosure ({a} : Set G)
  have haK : a ∈ K := subset_normalClosure (Set.mem_singleton a)
  have he : a * (c * a⁻¹ * c⁻¹) = c := by
    calc
      a * (c * a⁻¹ * c⁻¹) = (a * c) * a⁻¹ * c⁻¹ := by group
      _ = (c ^ 2 * a) * a⁻¹ * c⁻¹ := by rw [hi]
      _ = c := by group
  exact he ▸ K.mul_mem haK
    ((inferInstance : K.Normal).conj_mem a⁻¹ (K.inv_mem haK) c)

private theorem mem_zpowers_subgroup_iff (N : Subgroup G) (c x : N) :
    x ∈ zpowers c ↔ (x : G) ∈ zpowers (c : G) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext hn⟩

theorem sylow_normalizes_cubic_in_normal [Finite G]
    (S : Sylow 2 G) (N : Subgroup G) [N.Normal] (c : N)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers (c : G) : Set G)) :
    ∃ P : Sylow 2 N, (P : Subgroup N) = (S : Subgroup G).subgroupOf N ∧
      (P : Subgroup N) ≤ normalizer (zpowers c : Set N) := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal N
  refine ⟨P, hP, ?_⟩
  intro p hp
  have hs : (p : G) ∈ (S : Subgroup G) := by
    change p ∈ (S : Subgroup G).subgroupOf N
    rwa [← hP]
  apply mem_normalizer_iff.mpr
  intro x
  rw [mem_zpowers_subgroup_iff, mem_zpowers_subgroup_iff]
  exact mem_normalizer_iff.mp (hn hs) x

theorem binary_normalClosure_degree_of_normalized_inverted_cubic [Finite G]
    (a c : G) (S : Sylow 2 G) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hi : a * c = c ^ 2 * a)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G))
    {n : ℕ} (hnd : 2 ≤ n)
    (e : (normalClosure ({a} : Set G)) ≃* BinaryLinear.GL (Fin n → ZMod 2)) : n = 2 := by
  let c' : normalClosure ({a} : Set G) := ⟨c, inverted_element_mem_normalClosure a c hi⟩
  obtain ⟨P, _, hp⟩ := sylow_normalizes_cubic_in_normal S _ c' hn
  exact binary_actor_degree_of_normalized_cubic P c' (Subtype.ext hc)
    (fun he => hcne (congrArg Subtype.val he)) hp hnd e
end CFSG.Quasithin.ChapterG.Section06
