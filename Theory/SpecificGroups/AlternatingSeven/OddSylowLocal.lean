module
public import Theory.SpecificGroups.AlternatingSeven.SylowLocal
public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting.SymmetricFour
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-! The Sylow-invariant S4 in A7 lifts through every odd central cover. Its
characteristic complement in the inverse image contains the prescribed Sylow,
so automorphisms normalizing that Sylow preserve the lifted local subgroup.
The quotient still fails to centralize any permutation of cycle type 2³.
This is the local subgroup used in Aschbacher--Smith 2.5.2, printed p.551. -/
public section
namespace AlternatingSevenSylowLocal
open Equiv Subgroup
open Sporadic.Mathieu.M22ValueBound.OddCoverLifting
variable {L : Type*} [Group L] [Finite L]

/-- Lift the canonical S4 through an odd central kernel. The actual chosen
complement contains the prescribed Sylow and remains invariant under its
normalizing automorphisms. -/
theorem exists_invariant_local_of_odd_center
    (e : (L ⧸ center L) ≃* A7) (ho : Odd (Nat.card (center L))) (P : Sylow 2 L) :
    ∃ K : Subgroup L, (P : Subgroup L) ≤ K ∧
      Nonempty (K ≃* Perm (Fin 4)) ∧
      (∀ α : MulAut L, (P : Subgroup L).map α.toMonoidHom = P → K.map α.toMonoidHom = K) ∧
      ∀ σ : S7, σ.cycleType = {2,2,2} →
        ¬ ∀ k ∈ K, (e (QuotientGroup.mk' (center L) k) : S7) * σ =
          σ * e (QuotientGroup.mk' (center L) k) := by
  let q : L →* A7 := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkq : q.ker = center L := by
    ext x
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
    rw [← e.map_one,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let R := P.mapSurjective (f := q) hq
  obtain ⟨B,hPB,⟨eB⟩,hBinv,hBn⟩ := exists_invariant_local R
  let E := B.comap q
  let g : E →* B := (q.comp E.subtype).codRestrict B (fun x => x.property)
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨x,hx⟩ := hq b
    exact ⟨⟨x,show q x ∈ B from hx.symm ▸ b.property⟩,Subtype.ext hx⟩
  let f := eB.toMonoidHom.comp g
  have hf : Function.Surjective f := eB.surjective.comp hg
  have hk : f.ker = (center L).subgroupOf E := by
    ext x
    change eB (g x) = 1 ↔ (x : L) ∈ center L
    rw [← eB.map_one,eB.injective.eq_iff]
    rw [Subtype.ext_iff]
    change q x = 1 ↔ _
    exact show (x : L) ∈ q.ker ↔ _ from hkq ▸ Iff.rfl
  have hCE : center L ≤ E := by
    intro x hx
    change q x ∈ B
    rw [show q x = 1 from (hkq.symm ▸ hx : x ∈ q.ker)]
    exact B.one_mem
  have hfc : f.ker ≤ center E := by
    intro x hx
    rw [hk] at hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hx y))
  have hfo : Odd (Nat.card f.ker) := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hCE).toEquiv]
    exact ho
  obtain ⟨D,hDc,hDcpl,eD,heD⟩ := exists_characteristic_symmetric_four_complement f hf hfc hfo
  let : D.Characteristic := hDc
  let K := D.map E.subtype
  have hDgen : twoGenerated D = ⊤ := by
    apply map_injective (f := eD.toMonoidHom) eD.injective
    rw [twoGenerated_map_equiv eD,twoGenerated_perm,map_top_of_surjective _ eD.surjective]
  have hDeq : D = twoGenerated E := complement_eq_twoGenerated f.ker D hfc hfo hDcpl hDgen
  have hPE : (P : Subgroup L) ≤ E := by
    intro x hx
    exact hPB (mem_map_of_mem q hx)
  have hPK : (P : Subgroup L) ≤ K := by
    intro x hx
    refine ⟨⟨x,hPE hx⟩,?_,rfl⟩
    rw [hDeq]
    exact isPGroup_le_twoGenerated ((P : Subgroup L).subgroupOf E) P.isPGroup'.comap_subtype hx
  refine ⟨K,hPK,⟨(D.equivMapOfInjective E.subtype E.subtype_injective).symm.trans eD⟩,?_,?_⟩
  · intro α hα
    let β := (MulAut.congr e) ((center L).quotientAut α)
    have hcompat (x : L) : q (α x) = β (q x) := by
      change e (QuotientGroup.mk' (center L) (α x)) =
        e ((center L).quotientAut α (e.symm (e (QuotientGroup.mk' (center L) x))))
      rw [e.symm_apply_apply,quotientAut_apply_mk]
    have hR : (R : Subgroup A7).map β.toMonoidHom = R := by
      change ((P : Subgroup L).map q).map β.toMonoidHom = (P : Subgroup L).map q
      have he : β.toMonoidHom.comp q = q.comp α.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        exact (hcompat x).symm
      rw [map_map,he,← map_map,hα]
    have hB := hBinv β hR
    have hE : E.map α.toMonoidHom = E := by
      apply Subgroup.eq_of_le_of_card_ge ?_ (card_map_of_injective α.injective).ge
      rintro _ ⟨x,hx,rfl⟩
      change q (α x) ∈ B
      rw [hcompat]
      exact hB ▸ mem_map_of_mem β.toMonoidHom hx
    let δ : MulAut E := (α.subgroupMap E).trans (MulEquiv.subgroupCongr hE)
    have hd : D.map δ.toMonoidHom = D := characteristic_iff_map_eq.mp hDc δ
    have he : α.toMonoidHom.comp E.subtype = E.subtype.comp δ.toMonoidHom := by ext x;rfl
    change (D.map E.subtype).map α.toMonoidHom = D.map E.subtype
    rw [map_map,he,← map_map,hd]
  · intro σ hσ hfix
    apply hBn σ hσ
    intro b hb
    let d : D := eD.symm (eB ⟨b,hb⟩)
    have hd : g d = ⟨b,hb⟩ := eB.injective (by
      change f d = eB ⟨b,hb⟩
      rw [← heD,eD.apply_symm_apply])
    have hqd : q (d : E) = b := congrArg Subtype.val hd
    have hx := hfix (d : E) (mem_map_of_mem E.subtype d.property)
    change (q (d : E) : S7) * σ = σ * q (d : E) at hx
    rwa [hqd] at hx

end AlternatingSevenSylowLocal
