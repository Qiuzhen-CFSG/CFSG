module
public import Theory.GroupTheory.MarkedSemidirectProduct

/-!
# Keeping the selected complement map in split-product transport

The split-product equivalence agrees pointwise with the prescribed complement
isomorphism. This retains the marked cubic and rotation used by the original
normalizer comparison in Aschbacher (1994), 45.11, p.248.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G G' : Type*} [Group G] [Group G']
theorem exists_markedSemidirectTransport_restriction
    (N D K : Subgroup G) (hND : D ⊔ K = N)
    (hKD : K ≤ normalizer (D : Set G)) (hdis : Disjoint D K)
    (N' D' K' : Subgroup G') (hND' : D' ⊔ K' = N')
    (hKD' : K' ≤ normalizer (D' : Set G')) (hdis' : Disjoint D' K')
    (eD : D ≃* D') (eK : K ≃* K')
    (hact : ∀ k : K,
      ((D.normalizerMonoidHom.comp (inclusion hKD)) k).trans eD =
        eD.trans ((D'.normalizerMonoidHom.comp (inclusion hKD')) (eK k))) :
    ∃ e : N ≃* N',
      (D.subgroupOf N).map e.toMonoidHom = D'.subgroupOf N' ∧
      (K.subgroupOf N).map e.toMonoidHom = K'.subgroupOf N' ∧
      (∀ k : K, (e ⟨k,(hND ▸ le_sup_right) k.property⟩ : G')=(eK k : G')) := by
  let E := markedSemidirectEquiv N D K hND hKD hdis
  let E' := markedSemidirectEquiv N' D' K' hND' hKD' hdis'
  let T := SemidirectProduct.congr eD eK hact
  let e := E.symm.trans (T.trans E')
  have hDN : D ≤ N := hND ▸ le_sup_left
  have hKN : K ≤ N := hND ▸ le_sup_right
  have heD (d : D) : (e ⟨d,hDN d.property⟩ : G') = (eD d : G') := by
    have hd : E (SemidirectProduct.inl d) = ⟨d,hDN d.property⟩ := by
      apply Subtype.ext
      simp [E,markedSemidirectEquiv_apply]
    change (E' (T (E.symm _)) : G') = _
    rw [←hd,MulEquiv.symm_apply_apply]
    change (eD d : G') * (eK 1 : G') = _
    simp
  have heK (k : K) : (e ⟨k,hKN k.property⟩ : G') = (eK k : G') := by
    have hk : E (SemidirectProduct.inr k) = ⟨k,hKN k.property⟩ := by
      apply Subtype.ext
      simp [E,markedSemidirectEquiv_apply]
    change (E' (T (E.symm _)) : G') = _
    rw [←hk,MulEquiv.symm_apply_apply]
    change (eD 1 : G') * (eK k : G') = _
    simp
  refine ⟨e,?_,?_,heK⟩
  · apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      change (e x : G') ∈ D'
      have he := heD ⟨x,hx⟩
      change (e x : G') = _ at he
      rw [he]
      exact (eD ⟨x,hx⟩).property
    · intro y hy
      let d := eD.symm ⟨y,hy⟩
      refine ⟨⟨d,hDN d.property⟩,d.property,?_⟩
      apply Subtype.ext
      change (e ⟨d,hDN d.property⟩ : G') = (y:G')
      rw [heD]
      exact congrArg Subtype.val (eD.apply_symm_apply ⟨y,hy⟩)
  · apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      change (e x : G') ∈ K'
      have he := heK ⟨x,hx⟩
      change (e x : G') = _ at he
      rw [he]
      exact (eK ⟨x,hx⟩).property
    · intro y hy
      let k := eK.symm ⟨y,hy⟩
      refine ⟨⟨k,hKN k.property⟩,k.property,?_⟩
      apply Subtype.ext
      change (e ⟨k,hKN k.property⟩ : G') = (y:G')
      rw [heK]
      exact congrArg Subtype.val (eK.apply_symm_apply ⟨y,hy⟩)
end Theory.GroupTheory
