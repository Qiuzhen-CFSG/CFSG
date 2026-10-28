module
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# A normalized subgroup is covered by its residual and an ambient Sylow

Restrict the ambient Sylow to the product with the normalized subgroup,
then intersect with that normal subgroup. This gives its actual Sylow
intersection, so its prime residual and the original Sylow cover it.
Source application: the point-parabolic L₁T lift in Aschbacher–Smith13.3.18.
-/

public section

namespace Subgroup
variable {G:Type*} [Group G] [Finite G] {p:ℕ} [Fact p.Prime]

private theorem normalized_sylow_intersection (T:Sylow p G) (K:Subgroup G)
    (hTK:(T:Subgroup G)≤normalizer (K:Set G)) :
    ∃S:Sylow p K,(S:Subgroup K)=(T:Subgroup G).subgroupOf K := by
  let J:=K⊔(T:Subgroup G)
  have hKJ:K≤J:=le_sup_left
  let :(K.subgroupOf J).Normal:=normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer hTK)
  obtain ⟨P,hP⟩:=(T.subtype (show (T:Subgroup G)≤J from le_sup_right)).exists_subgroupOf_eq_of_normal
    (K.subgroupOf J)
  let e:=subgroupOfEquivOfLe hKJ
  refine ⟨P.mapSurjective (f:=e.toMonoidHom) e.surjective,?_⟩
  change (P:Subgroup (K.subgroupOf J)).map e.toMonoidHom=_
  rw [hP]
  ext k
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha
  · intro hk
    exact ⟨⟨⟨k,hKJ k.prop⟩,k.prop⟩,hk,rfl⟩

theorem le_embedded_pResidual_sup_sylow_of_normalizes
    (T:Sylow p G) (K:Subgroup G) (hTK:(T:Subgroup G)≤normalizer (K:Set G)) :
    K≤(pResidual p K).map K.subtype⊔(T:Subgroup G) := by
  obtain ⟨S,hS⟩:=normalized_sylow_intersection T K hTK
  have hs:=congrArg (Subgroup.map K.subtype) (pResidual_sup_sylow_eq_top S)
  rw [map_sup,←MonoidHom.range_eq_map,range_subtype,hS,subgroupOf_map_subtype] at hs
  exact hs.symm.le.trans (sup_le le_sup_left (inf_le_left.trans le_sup_right))
end Subgroup
