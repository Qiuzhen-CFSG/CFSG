module
public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting.SymmetricFour
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
/-! Lift an actual symmetric-four subgroup through an odd central kernel.
The characteristic complement supplied by the Coxeter splitting is preserved
by every compatible pair of automorphisms stabilizing the quotient subgroup.
The restricted map is injective and has exactly the prescribed image.
Source application: the A6 and triple-A6 parabolics in Aschbacher--Smith
2.5.2, printed p.551. -/
public section
open Subgroup
namespace Sporadic.Mathieu.M22ValueBound.OddCoverLifting
variable {L B : Type*} [Group L] [Group B] [Finite L]

theorem exists_invariant_symmetric_four_lift (q : L →* B) (hq : Function.Surjective q)
    (hc : q.ker ≤ center L) (ho : Odd (Nat.card q.ker))
    (U : Subgroup B) (eU : U ≃* Equiv.Perm (Fin 4)) :
    ∃ K : Subgroup L, Nonempty (K ≃* Equiv.Perm (Fin 4)) ∧ K.map q = U ∧
      Function.Injective (q.comp K.subtype) ∧
      ∀ (α : MulAut L) (β : MulAut B),
        (∀ x, q (α x) = β (q x)) → U.map β.toMonoidHom = U → K.map α.toMonoidHom = K := by
  let E := U.comap q
  let g : E →* U := (q.comp E.subtype).codRestrict U (fun x => x.property)
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨x,hx⟩ := hq b
    exact ⟨⟨x,show q x ∈ U from hx.symm ▸ b.property⟩,Subtype.ext hx⟩
  let f := eU.toMonoidHom.comp g
  have hf : Function.Surjective f := eU.surjective.comp hg
  have hk : f.ker = q.ker.subgroupOf E := by
    ext x
    change eU (g x) = 1 ↔ q x = 1
    rw [← eU.map_one,eU.injective.eq_iff]
    exact Subtype.ext_iff
  have hCE : q.ker ≤ E := by
    intro x hx
    change q x ∈ U
    rw [show q x=1 from hx]
    exact U.one_mem
  have hfc : f.ker ≤ center E := by
    intro x hx
    rw [hk] at hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hc hx) y))
  have hfo : Odd (Nat.card f.ker) := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hCE).toEquiv]
    exact ho
  obtain ⟨D,hDc,hDcpl,eD,heD⟩ := exists_characteristic_symmetric_four_complement f hf hfc hfo
  let K := D.map E.subtype
  let eK := (D.equivMapOfInjective E.subtype E.subtype_injective).symm.trans eD
  have hKq : K.map q = U := by
    apply le_antisymm
    · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact x.property
    · intro u hu
      let d : D := eD.symm (eU ⟨u,hu⟩)
      have hd : g d = ⟨u,hu⟩ := eU.injective (by
        change f d = eU ⟨u,hu⟩
        rw [← heD,eD.apply_symm_apply])
      exact ⟨d.val.val,mem_map_of_mem E.subtype d.property,congrArg Subtype.val hd⟩
  refine ⟨K,⟨eK⟩,hKq,?_,?_⟩
  · intro x y hxy
    obtain ⟨a,ha,heax⟩ := x.property
    obtain ⟨b,hb,heby⟩ := y.property
    have hab : (⟨a,ha⟩ : D) = ⟨b,hb⟩ := by
      apply eD.injective
      rw [heD,heD]
      apply congrArg eU
      apply Subtype.ext
      change q a.val=q b.val
      change q (x : L)=q (y : L) at hxy
      change (a : L)=(x : L) at heax
      change (b : L)=(y : L) at heby
      rwa [heax,heby]
    exact Subtype.ext (heax.symm.trans ((congrArg (fun d:D => d.val.val) hab).trans heby))
  · intro α β hcompat hU
    have hE : E.map α.toMonoidHom = E := by
      apply eq_of_le_of_card_ge ?_ (card_map_of_injective α.injective).ge
      rintro _ ⟨x,hx,rfl⟩
      change q (α x) ∈ U
      rw [hcompat]
      exact hU ▸ mem_map_of_mem β.toMonoidHom hx
    let δ : MulAut E := (α.subgroupMap E).trans (MulEquiv.subgroupCongr hE)
    have hd : D.map δ.toMonoidHom = D := characteristic_iff_map_eq.mp hDc δ
    have he : α.toMonoidHom.comp E.subtype = E.subtype.comp δ.toMonoidHom := by ext x;rfl
    change (D.map E.subtype).map α.toMonoidHom = D.map E.subtype
    rw [map_map,he,← map_map,hd]
end Sporadic.Mathieu.M22ValueBound.OddCoverLifting
