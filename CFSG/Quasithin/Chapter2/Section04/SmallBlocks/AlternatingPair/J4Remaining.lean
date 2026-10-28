module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Remaining
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.HS_Held.Held

/-! Held's native cubic-centralizer exclusion leaves only J4 for the actual
ordinary component of the original paired alternating-five configuration.
Source: Aschbacher--Smith 2.4.25, printed pp.541--543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The two remaining ordinary-component rows for the original paired block. -/
theorem MinimalBlockSetup.alternating_five_pair_j4
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hpair : d.L0 ≠ d.block) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∃ K : Subgroup GI, IsComponent GI K ∧ L.subgroupOf GI ≤ K ∧
      SI S L ≤ normalizer (K.map GI.subtype : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* ClassificationModels.SporadicName.j4.Carrier) := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c⟩ := d.alternating_pair_configuration hG T hST.le hpair hA M₀ hSM hMT hi
  obtain ⟨K,hK,hLK,hNK⟩ := c.phi_ordinary_component hG T hM hTM hu hST.le hSM hMT hi
  obtain ⟨n,hn,hm⟩ := c.ordinary_overcomponent_remaining hG T hM hTM hu hST.le hSM hMT hi K hK hLK hNK
  rcases hn with rfl | rfl
  · exact ⟨K,hK,hLK,hNK,hm⟩
  · exact (c.held_overcomponent_false hG T hM hTM hu hST.le hSM hMT hi K hK hLK hNK hm).elim
end CFSG.Quasithin.Chapter2
