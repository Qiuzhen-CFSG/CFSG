module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.BinaryFiveSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Projection
/-!
# The binary-five row in the original paired A₅ configuration

The literal ordinary component contains the original block and is normalized
by its original stabilizer S_I. Transport the block layer through that same
inclusion and the central quotient model, then apply the canonical elementary
sixteen normalizer obstruction. No full Sylow bound on the component is used.

Source: Aschbacher–Smith 2.4.25, printed p.543.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

/-- The binary-five row of the original paired-block terminal statement. -/
theorem AlternatingPairSourceSetup.binary_five_overcomponent_false
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
      ClassicalGroup.IsPSL (K ⧸ center K) 5 2 → False := by
  intro S L GI K hK hLK hNK hm
  let E := K.map GI.subtype
  let f : K ≃* E := K.equivMapOfInjective GI.subtype GI.subtype_injective
  let := hK.2
  let : IsQuasisimple E := IsQuasisimple.of_mulEquiv f
  have hLG : L ≤ GI := (c.phi_normalizer_source hG T hM hTM hu hST hSM hMT hi).2.2.2.1.trans
    (Subgroup.centralizer_le_normalizer _)
  have hLE : L ≤ E := by
    intro l hl
    exact ⟨⟨l,hLG hl⟩,hLK hl,rfl⟩
  have hcenter : (center K).map f.toMonoidHom = center E := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr f ⟨x,hx⟩).property
    · intro x hx
      exact ⟨f.symm x,(centerCongr f).symm ⟨x,hx⟩ |>.property,f.apply_symm_apply x⟩
  have hmodel : ClassicalGroup.IsPSL (E ⧸ center E) 5 2 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,
      ⟨(QuotientGroup.congr _ _ f hcenter).symm.trans e⟩⟩
  let A := L.subgroupOf E
  let a : A ≃* L := subgroupOfEquivOfLe hLE
  have hA : IsAlternatingBlock A 5 := RankOne.Solvable.isAlternatingBlock_of_equiv a.symm c.marked₁.block
  have hUa : ((blockU A).map A.subtype).map E.subtype = sourceModule L := by
    change ((blockU A).map A.subtype).map E.subtype = (blockU L).map L.subtype
    rw [←RankOne.Solvable.blockU_map_equiv a,map_map,map_map]
    rfl
  have hc : Nat.card ((blockU A).map A.subtype) = 16 := by
    rw [←card_map_of_injective E.subtype_injective,hUa]
    exact c.marked₁.module_card
  obtain ⟨hhalf,_,hQ,hbeta⟩ := c.stabilizer_base hG T hM hTM hu hST hSM hMT hi
  exact d.alternating_no_binary_five_component hG T hTM hu inf_le_left hhalf hbeta
    (c.stabilizer_local_component hQ) hLE hNK inf_le_right hA hc hmodel
end CFSG.Quasithin.Chapter2
