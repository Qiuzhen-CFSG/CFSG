module
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Proper overgroups of a Sylow in a rank-one supplement

Let K be normalized by an ambient Sylow two-subgroup T, with a surjection
K → SL₂(F) over a finite field of characteristic two and a two-group kernel.
Every proper overgroup of T in K join T lies in N_K(T intersection K) join T.
The rank-one Borel theorem applies inside K; relative normality then factors
an element of the overgroup into its K-part and its T-part.

This supplies the minimal-parabolic application in Aschbacher--Smith
14.3.6(1), printed p.991 (`refs/quasithin.pdf`), without assuming T ≤ K.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Proper overgroups of the original Sylow in `K ⊔ T` lie in the join of
`T` and the actual normalizer of `T ∩ K` inside `K`. -/
theorem proper_overgroup_join_le_borel_sup
    (T : Sylow 2 G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (q : K →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (Y : Subgroup G) (hTY : (T : Subgroup G) ≤ Y)
    (hY : Y < K ⊔ (T : Subgroup G)) :
    Y ≤ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ⊔
      (T : Subgroup G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  have hPK : (P : Subgroup K) ≤ Y.subgroupOf K := by
    rw [hP]
    exact fun _ hx => hTY hx
  have hproper : Y.subgroupOf K ≠ ⊤ := by
    intro he
    have hKY : K ≤ Y := by
      intro k hk
      exact show (⟨k,hk⟩ : K) ∈ Y.subgroupOf K from (by rw [he]; trivial)
    exact hY.not_ge (sup_le hKY hTY)
  have hYN := proper_overgroup_le_sylow_normalizer_of_two_kernel q hq P
    (hk.le_sylow_of_normal P) (Y.subgroupOf K) hPK hproper
  have hYP : Y.subgroupOf K ≤ normalizer ((T : Subgroup G).subgroupOf K : Set K) := by
    change Y.subgroupOf K ≤ normalizer ((P : Subgroup K) : Set K) at hYN
    rwa [hP] at hYN
  let H := K ⊔ (T : Subgroup G)
  have hKH : K ≤ H := le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  let : (K.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  have hgen : K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map, range_subtype]
  intro y hy
  have hyH : (⟨y,hY.le hy⟩ : H) ∈ K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H := by
    rw [hgen]
    trivial
  obtain ⟨k,hk,t,ht,hkt⟩ := mem_sup_of_normal_left.mp hyH
  have hktG : (k : G) * (t : G) = y := congrArg Subtype.val hkt
  have hkY : (k : G) ∈ Y := by
    have hmem := Y.mul_mem hy (Y.inv_mem (hTY ht))
    rw [← hktG] at hmem
    change (k : G) * (t : G) * (t : G)⁻¹ ∈ Y at hmem
    simpa only [mul_inv_cancel_right] using hmem
  rw [← hktG]
  exact mul_mem_sup (mem_map_of_mem K.subtype (hYP (show (⟨k,hk⟩ : K) ∈ Y.subgroupOf K from hkY))) ht

end Matrix.SpecialLinearGroup
