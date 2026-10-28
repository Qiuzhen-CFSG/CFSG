module
public import Mathlib.GroupTheory.SemidirectProduct
/-!
# Transport of marked internal semidirect products

For disjoint subgroups D and K with K normalizing D, multiplication
identifies the external semidirect product with their actual join. Compatible
isomorphisms of both factors therefore extend to the joins and carry both
marked subgroups exactly to their target subgroups.

This is the extension step used for the cubic-line normalizers in
Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]
/-- The original multiplication map identifies the split product with N. -/
noncomputable def markedSemidirectEquiv
    (N D K : Subgroup G) (hND : D ⊔ K = N)
    (hKD : K ≤ normalizer (D : Set G)) (hdis : Disjoint D K) :
    D ⋊[D.normalizerMonoidHom.comp (inclusion hKD)] K ≃* N := by
  let f := SemidirectProduct.monoidHomSubgroup hKD
  let j := f.codRestrict N (fun a => hND ▸ (D ⊔ K).mul_mem
    (show (a.left:G) ∈ D ⊔ K from mem_sup_left a.left.property)
    (show (a.right:G) ∈ D ⊔ K from mem_sup_right a.right.property))
  exact MulEquiv.ofBijective j ⟨by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    apply bot_unique
    intro a ha
    have he : (a.left:G) * (a.right:G) = 1 := congrArg Subtype.val ha
    have hl : (a.left:G) = 1 := hdis.le_bot ⟨a.left.property,
      (mul_eq_one_iff_eq_inv.mp he) ▸ K.inv_mem a.right.property⟩
    have hr : (a.right:G) = 1 := by simpa only [hl,one_mul] using he
    apply mem_bot.mpr
    exact SemidirectProduct.ext (Subtype.ext hl) (Subtype.ext hr), by
    intro n
    have hn : (n:G) ∈ (D:Set G) * (K:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left D K hKD]
      exact hND.symm ▸ n.property
    obtain ⟨d,hd,k,hk,hdk⟩ := hn
    exact ⟨⟨⟨d,hd⟩,⟨k,hk⟩⟩,Subtype.ext hdk⟩⟩

@[simp] theorem markedSemidirectEquiv_apply
    (N D K : Subgroup G) (hND : D ⊔ K = N)
    (hKD : K ≤ normalizer (D : Set G)) (hdis : Disjoint D K)
    (a : D ⋊[D.normalizerMonoidHom.comp (inclusion hKD)] K) :
    (markedSemidirectEquiv N D K hND hKD hdis a : G) = (a.left:G) * (a.right:G) := rfl

variable {G' : Type*} [Group G']
/-- Compatible isomorphisms of the actual factors extend to their split products,
with both original subgroups carried to the prescribed target subgroups. -/
theorem exists_markedSemidirectTransport
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
      (K.subgroupOf N).map e.toMonoidHom = K'.subgroupOf N' := by
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
  refine ⟨e,?_,?_⟩
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
