module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.ImageMarks
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.InvariantTransfer
/-!
# The literal paired-block consumers of model escaping overgroups

The faithful image retains the actual deleted-five block and its elementary
sixteen. A model isomorphism transports the full local obstruction and, for
an invariant escape, conjugates the original automorphism action. Pullback
through the component two-core therefore supplies the exact SI-normalized
ambient overgroup contradicted by starred persistence.

Source: Aschbacher–Smith 2.4.25, printed p.543. The family row producers
supply the model premises used by the final terminal census.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
open ChapterC
variable {E D : Type*} [Group E] [Group D]
/-- The block layer has the same literal image under a map faithful on the block. -/
theorem blockU_image_of_injective_restriction (A : Subgroup E) (q : E →* D)
    (hi : Function.Injective (q.comp A.subtype)) :
    (blockU (A.map q)).map (A.map q).subtype = ((blockU A).map A.subtype).map q := by
  have hr : (q.comp A.subtype).range = A.map q := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  let e : A ≃* A.map q := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)
  rw [←RankOne.Solvable.blockU_map_equiv e,map_map,map_map]
  rfl

/-- Carry the entire invariant escaping overgroup through the specified model isomorphism. -/
theorem invariant_obstruction_of_equiv [Finite E] [Finite D]
    (e : E ≃* D) (A : Subgroup E)
    (N' : Subgroup D) (hN' : N' ∈ Chapter1.He D) (hAN' : A.map e.toMonoidHom ≤ N')
    (hInv' : ∀ b : MulAut D,
      ((blockU (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype).map b.toMonoidHom =
        (blockU (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype →
      N'.map b.toMonoidHom = N')
    (hbad' : ∀ Q : Sylow 2 N', (A.map e.toMonoidHom).subgroupOf N' ∉
      ChapterA.Section03.localCComponents Q) :
    ∃ N : Subgroup E, N ∈ Chapter1.He E ∧ A ≤ N ∧
      (∀ a : MulAut E, ((blockU A).map A.subtype).map a.toMonoidHom =
        (blockU A).map A.subtype → N.map a.toMonoidHom = N) ∧
      ∀ Q : Sylow 2 N, A.subgroupOf N ∉ ChapterA.Section03.localCComponents Q := by
  let N := N'.comap e.toMonoidHom
  have hNN : N.map e.toMonoidHom = N' := map_comap_eq_self_of_surjective e.surjective N'
  have hAN : A ≤ N := by
    intro x hx
    exact hAN' (mem_map_of_mem e.toMonoidHom hx)
  let f : N ≃* N' := (N.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hNN)
  have hN : N ∈ Chapter1.He E := Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 f).mpr (Chapter1.mem_He_iff.mp hN'))
  refine ⟨N,hN,hAN,?_,?_⟩
  · intro a ha
    let b := MulAut.congr e a
    have hcomm : e.toMonoidHom.comp a.toMonoidHom = b.toMonoidHom.comp e.toMonoidHom := by
      ext x
      change e (a x) = e (a (e.symm (e x)))
      rw [e.symm_apply_apply]
    have hUb : ((blockU (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype).map
        b.toMonoidHom = (blockU (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype := by
      rw [blockU_image_of_injective_restriction A e.toMonoidHom
        (e.injective.comp A.subtype_injective),map_map,←hcomm,←map_map,ha]
    have hNb := hInv' b hUb
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_map,hcomm,←map_map,hNN,hNb]
  · intro Q hl
    let : Group.IsSolvable f.toMonoidHom.ker := by
      rw [f.toMonoidHom.ker_eq_bot f.injective]; infer_instance
    have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
    have he : (A.subgroupOf N).map f.toMonoidHom = (A.map e.toMonoidHom).subgroupOf N' := by
      ext x
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact mem_map_of_mem e.toMonoidHom ha
      · rintro ⟨a,ha,he⟩
        exact ⟨⟨a,hAN ha⟩,ha,Subtype.ext he⟩
    have hfs : Function.Surjective f.toMonoidHom := f.surjective
    apply hbad' (Q.mapSurjective hfs)
    rw [Sylow.coe_mapSurjective]
    exact he ▸ hm
end CFSG.Quasithin.Chapter2.AlternatingTerminal
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}
theorem AlternatingPairSourceSetup.quotient_normalizer_overcomponent_false
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
    ∀ {D : Type*} [Group D] [Finite D],
    (∀ B : Subgroup D, IsAlternatingBlock B 5 → Nat.card ((blockU B).map B.subtype) = 16 →
      let N := normalizer ((blockU B).map B.subtype : Set D)
      N ∈ Chapter1.He D ∧ ∀ Q : Sylow 2 N,
        B.subgroupOf N ∉ ChapterA.Section03.localCComponents Q) →
    Nonempty ((K ⧸ pCore 2 K) ≃* D) → False := by
  intro S L GI K hK hLK hNK D _ _ hrow hmodel
  let E := K.map GI.subtype
  let f : K ≃* E := K.equivMapOfInjective GI.subtype GI.subtype_injective
  obtain ⟨eK⟩ := hmodel
  let e : (E ⧸ pCore 2 E) ≃* D :=
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm.trans eK
  obtain ⟨hLE,hA,hc,hqi,hAQ,hcQ⟩ := c.block_image_component_twoCore_quotient_marks
    hG T hM hTM hu hST hSM hMT hi K hK hLK
  let A := L.subgroupOf E
  let q := QuotientGroup.mk' (pCore 2 E)
  let B := (A.map q).map e.toMonoidHom
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv
    ((A.map q).equivMapOfInjective e.toMonoidHom e.injective) hAQ
  have hcB : Nat.card ((blockU B).map B.subtype) = 16 := by
    rw [AlternatingTerminal.blockU_image_of_injective_restriction _ _
      (e.injective.comp (A.map q).subtype_injective),card_map_of_injective e.injective]
    exact hcQ
  obtain ⟨hN,hbad⟩ := hrow B hB hcB
  obtain ⟨hNQ,hbadQ⟩ := AlternatingTerminal.normalizer_obstruction_of_equiv e (A.map q) hN hbad
  have hU := AlternatingTerminal.blockU_image_of_injective_restriction A q hqi
  obtain ⟨hhalf,_,hQ,hbeta⟩ := c.stabilizer_base hG T hM hTM hu hST hSM hMT hi
  apply d.alternating_no_component_quotient_normalizer_obstruction hG T hTM hu
    inf_le_left hhalf hbeta (c.stabilizer_local_component hQ) hLE hNK inf_le_right
  · rw [←hU]; exact hNQ
  · rw [←hU]; exact hbadQ
theorem AlternatingPairSourceSetup.invariant_quotient_overcomponent_false
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
    ∀ {D : Type*} [Group D] [Finite D],
    (∀ B : Subgroup D, IsAlternatingBlock B 5 → Nat.card ((blockU B).map B.subtype) = 16 →
      ∃ N : Subgroup D, N ∈ Chapter1.He D ∧ B ≤ N ∧
        (∀ b : MulAut D, ((blockU B).map B.subtype).map b.toMonoidHom =
          (blockU B).map B.subtype → N.map b.toMonoidHom = N) ∧
        ∀ Q : Sylow 2 N, B.subgroupOf N ∉ ChapterA.Section03.localCComponents Q) →
    Nonempty ((K ⧸ pCore 2 K) ≃* D) → False := by
  intro S L GI K hK hLK hNK D _ _ hrow hmodel
  let E := K.map GI.subtype
  let f : K ≃* E := K.equivMapOfInjective GI.subtype GI.subtype_injective
  obtain ⟨eK⟩ := hmodel
  let e : (E ⧸ pCore 2 E) ≃* D :=
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm.trans eK
  obtain ⟨hLE,hA,hc,hqi,hAQ,hcQ⟩ := c.block_image_component_twoCore_quotient_marks
    hG T hM hTM hu hST hSM hMT hi K hK hLK
  let A := L.subgroupOf E
  let q := QuotientGroup.mk' (pCore 2 E)
  let B := (A.map q).map e.toMonoidHom
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv
    ((A.map q).equivMapOfInjective e.toMonoidHom e.injective) hAQ
  have hcB : Nat.card ((blockU B).map B.subtype) = 16 := by
    rw [AlternatingTerminal.blockU_image_of_injective_restriction _ _
      (e.injective.comp (A.map q).subtype_injective),card_map_of_injective e.injective]
    exact hcQ
  obtain ⟨N,hN,hBN,hinv,hbad⟩ := hrow B hB hcB
  obtain ⟨W,hW,hAW,hinvW,hbadW⟩ :=
    AlternatingTerminal.invariant_obstruction_of_equiv e (A.map q) N hN hBN hinv hbad
  have hU := AlternatingTerminal.blockU_image_of_injective_restriction A q hqi
  obtain ⟨hhalf,_,hQ,hbeta⟩ := c.stabilizer_base hG T hM hTM hu hST hSM hMT hi
  apply d.alternating_no_component_invariant_quotient_obstruction hG T hTM hu
    inf_le_left hhalf hbeta (c.stabilizer_local_component hQ) hLE hNK inf_le_right
    W hW hAW
  · rw [←hU]; exact hinvW
  · exact hbadW
theorem AlternatingPairSourceSetup.no_block_quotient_overcomponent_false
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
    ∀ {D : Type*} [Group D] [Finite D],
    (∀ B : Subgroup D, IsAlternatingBlock B 5 → Nat.card ((blockU B).map B.subtype) = 16 → False) →
    Nonempty ((K ⧸ pCore 2 K) ≃* D) → False := by
  intro S L GI K hK hLK _ D _ _ hrow hmodel
  obtain ⟨e⟩ := hmodel
  obtain ⟨_,_,_,hAQ,hcQ⟩ := c.block_component_twoCore_quotient_marks
    hG T hM hTM hu hST hSM hMT hi K hK hLK
  let A := (L.subgroupOf GI).subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := (A.map q).map e.toMonoidHom
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv
    ((A.map q).equivMapOfInjective e.toMonoidHom e.injective) hAQ
  apply hrow B hB
  rw [AlternatingTerminal.blockU_image_of_injective_restriction _ _
    (e.injective.comp (A.map q).subtype_injective),card_map_of_injective e.injective]
  exact hcQ

theorem AlternatingPairSourceSetup.no_block_overcomponent_false
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
    ∀ {D : Type*} [Group D] [Finite D],
    (∀ B : Subgroup D, IsAlternatingBlock B 5 → Nat.card ((blockU B).map B.subtype) = 16 → False) →
    Nonempty (K ≃* D) → False := by
  intro S L GI K hK hLK _ D _ _ hrow hmodel
  obtain ⟨e⟩ := hmodel
  obtain ⟨hA,hc,_,_,_⟩ := c.block_component_twoCore_quotient_marks
    hG T hM hTM hu hST hSM hMT hi K hK hLK
  let A := (L.subgroupOf GI).subgroupOf K
  let B := A.map e.toMonoidHom
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv
    (A.equivMapOfInjective e.toMonoidHom e.injective) hA
  apply hrow B hB
  rw [AlternatingTerminal.blockU_image_of_injective_restriction _ _
    (e.injective.comp A.subtype_injective),card_map_of_injective e.injective]
  exact hc
end CFSG.Quasithin.Chapter2
