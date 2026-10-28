module
public import Theory.GroupTheory.InnerActionNormalizerSylow
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.SourceTransfers
/-! The original half-Sylow group acts on the ordinary component's two-core
quotient. If the quotient is centerless with only inner automorphisms, its
unique inner representatives lie in a Sylow of the faithful block normalizer.
An escaping characteristic-two overgroup containing that Sylow pulls back
through the two-core and remains invariant under the original actor. Starred
persistence contradicts its full-Sylow local-component obstruction.

This is the literal source consumer of the independent native J4 placement
row; no assertion about triviality of the component's cover is needed.
Source: Aschbacher--Smith 2.4.25, printed pp.542--543. -/
public section
open Subgroup

namespace CFSG.Quasithin.Chapter2
open Theory.GroupTheory ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

/-- A model escape containing a Sylow of the faithful quotient-block normalizer
lifts through the two-core while retaining the original half-Sylow actor. -/
theorem AlternatingPairSourceSetup.inner_quotient_overcomponent_false
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
    SI S L ≤ normalizer (K.map GI.subtype : Set G) →
    ∀ {D : Type*} [Group D] [Finite D], center D = ⊥ →
    Function.Surjective (MulAut.conj : D →* MulAut D) →
    (∀ B : Subgroup D, IsAlternatingBlock B 5 → Nat.card ((blockU B).map B.subtype) = 16 →
      ∀ P : Sylow 2 (normalizer (B : Set D)), ∃ N : Subgroup D,
        B ≤ N ∧ (P : Subgroup (normalizer (B : Set D))).map
          (normalizer (B : Set D)).subtype ≤ N ∧
        N ∈ Chapter1.He D ∧ ∀ Q : Sylow 2 N,
          B.subgroupOf N ∉ ChapterA.Section03.localCComponents Q) →
    Nonempty ((K ⧸ pCore 2 K) ≃* D) → False := by
  intro S L GI K hK hLK hNK D _ _ hc hin hrow ⟨eK⟩
  let E := K.map GI.subtype
  let f : K ≃* E := K.equivMapOfInjective GI.subtype GI.subtype_injective
  let e : (E ⧸ pCore 2 E) ≃* D :=
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm.trans eK
  obtain ⟨hLE,_,_,_,hAQ,hcQ⟩ := c.block_image_component_twoCore_quotient_marks
    hG T hM hTM hu hST hSM hMT hi K hK hLK
  let A := L.subgroupOf E
  let q₀ := QuotientGroup.mk' (pCore 2 E)
  let q := e.toMonoidHom.comp q₀
  let B := A.map q
  have hB : IsAlternatingBlock B 5 := by
    change IsAlternatingBlock (A.map (e.toMonoidHom.comp q₀)) 5
    rw [←map_map]
    exact RankOne.Solvable.isAlternatingBlock_of_equiv
      ((A.map q₀).equivMapOfInjective e.toMonoidHom e.injective) hAQ
  have hcB : Nat.card ((blockU B).map B.subtype) = 16 := by
    have hBeq : B = (A.map q₀).map e.toMonoidHom := (map_map _ _ _).symm
    rw [hBeq,AlternatingTerminal.blockU_image_of_injective_restriction _ _
      (e.injective.comp (A.map q₀).subtype_injective),card_map_of_injective e.injective]
    exact hcQ
  let R := SI S L
  have hRp : IsPGroup 2 R := (d.S.isPGroup'.map d.H.subtype).to_le inf_le_left
  let α : R →* MulAut E := E.normalizerMonoidHom.comp (inclusion hNK)
  let a : R →* MulAut D := (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (pCore 2 E)).comp α)
  have hcomm (r : R) : q.comp (α r).toMonoidHom = (a r).toMonoidHom.comp q := by
    ext x
    change e (q₀ (α r x)) = e (quotientAut (pCore 2 E) (α r) (e.symm (e (q₀ x))))
    rw [e.symm_apply_apply,quotientAut_apply_mk]
  have hAA (r : R) : A.map (α r).toMonoidHom = A := by
    apply map_injective E.subtype_injective
    rw [map_map]
    change A.map ((MulAut.conj (r : G)).toMonoidHom.comp E.subtype) = A.map E.subtype
    have hAE : A.map E.subtype = L := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact hy
      · intro hx; exact ⟨⟨x,hLE hx⟩,hx,rfl⟩
    rw [←map_map,hAE]
    exact mem_normalizer_iff_map_conj_eq.mp (show (r : G) ∈ normalizer (L : Set G) from r.property.2)
  have hBA (r : R) : B.map (a r).toMonoidHom = B := by
    change (A.map q).map (a r).toMonoidHom = A.map q
    rw [map_map,←hcomm,←map_map,hAA]
  obtain ⟨P,hP⟩ := exists_inner_action_normalizer_sylow a hRp B hc hin hBA
  obtain ⟨N,hBN,hPN,hN,hbad⟩ := hrow B hB hcB P
  have hker : IsPGroup 2 q.ker := by
    rw [show q = e.toMonoidHom.comp q₀ from rfl,
      MonoidHom.ker_comp_of_injective q₀ e.toMonoidHom e.injective]
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 E)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨hW,hAW,hbadW⟩ := AlternatingTerminal.quotient_overgroup_obstruction
    q (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker A N hBN hN hbad
  let W := N.comap q
  let V := W.map E.subtype
  have hRV : R ≤ normalizer (V : Set G) := by
    intro r hr
    have hNa := hP N hPN (⟨r,hr⟩ : R)
    have hWa : W.map (α ⟨r,hr⟩).toMonoidHom = W := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        change q (α ⟨r,hr⟩ y) ∈ N
        have hh := DFunLike.congr_fun (hcomm ⟨r,hr⟩) y
        change q (α ⟨r,hr⟩ y) = a ⟨r,hr⟩ (q y) at hh
        rw [hh]
        exact hNa ▸ mem_map_of_mem (a ⟨r,hr⟩).toMonoidHom hy
      · intro hx
        have hh : (a ⟨r,hr⟩).symm (q x) ∈ N := by
          obtain ⟨y,hy,he⟩ := show q x ∈ N.map (a ⟨r,hr⟩).toMonoidHom from hNa.symm ▸ hx
          change a ⟨r,hr⟩ y = q x at he
          rw [←he,(a ⟨r,hr⟩).symm_apply_apply]
          exact hy
        refine ⟨(α ⟨r,hr⟩).symm x,?_,(α ⟨r,hr⟩).apply_symm_apply x⟩
        change q ((α ⟨r,hr⟩).symm x) ∈ N
        have he : q ((α ⟨r,hr⟩).symm x) = (a ⟨r,hr⟩).symm (q x) := by
          apply (a ⟨r,hr⟩).injective
          rw [(a ⟨r,hr⟩).apply_symm_apply]
          have hh := DFunLike.congr_fun (hcomm ⟨r,hr⟩) ((α ⟨r,hr⟩).symm x)
          change q (α ⟨r,hr⟩ ((α ⟨r,hr⟩).symm x)) = a ⟨r,hr⟩ (q ((α ⟨r,hr⟩).symm x)) at hh
          rw [(α ⟨r,hr⟩).apply_symm_apply] at hh
          exact hh.symm
        exact he ▸ hh
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (W.map E.subtype).map (MulAut.conj r).toMonoidHom = W.map E.subtype
    rw [map_map]
    change W.map (E.subtype.comp (α ⟨r,hr⟩).toMonoidHom) = W.map E.subtype
    rw [←map_map,hWa]
  have hLV : L ≤ V := by
    intro l hl
    exact ⟨⟨l,hLE hl⟩,hAW hl,rfl⟩
  let eW : W ≃* V := W.equivMapOfInjective E.subtype E.subtype_injective
  have hV : V ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 eW).mp (Chapter1.mem_He_iff.mp hW))
  obtain ⟨hhalf,_,hQ,hbeta⟩ := c.stabilizer_base hG T hM hTM hu hST hSM hMT hi
  apply d.alternating_no_normalized_local_obstruction hG T hTM hu
    inf_le_left hhalf hbeta (c.stabilizer_local_component hQ) hV hLV hRV
  intro Q hlocal
  let : Group.IsSolvable eW.symm.toMonoidHom.ker := by
    rw [eW.symm.toMonoidHom.ker_eq_bot eW.symm.injective]
    infer_instance
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal eW.symm.toMonoidHom
  have he : (L.subgroupOf V).map eW.symm.toMonoidHom = A.subgroupOf W := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      have hh := congrArg (fun v : V => v.val) (eW.apply_symm_apply v)
      change (eW.symm v).val.val ∈ L
      exact hh ▸ hv
    · intro hw
      exact ⟨eW w,hw,eW.symm_apply_apply w⟩
  have hes : Function.Surjective eW.symm.toMonoidHom := eW.symm.surjective
  apply hbadW (Q.mapSurjective hes)
  rw [Sylow.coe_mapSurjective]
  exact he ▸ hm
end CFSG.Quasithin.Chapter2
