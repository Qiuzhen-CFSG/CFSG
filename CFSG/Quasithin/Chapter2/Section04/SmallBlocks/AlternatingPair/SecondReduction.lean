module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Ordinary
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.J4Remaining
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.JankoFour.Original

/-! The complete original paired-alternating-five argument reduces to the
second native J4 involution-centralizer leaf. All catalogue rows, original
half-Sylow normalization, even-centralizer placement, and starred persistence
are instantiated here. The separate matrix-action producer discharges the
single remaining local obstruction.
Source: Aschbacher--Smith 2.4.25, printed pp.541--543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Source 2.4.25: the original selected alternating-five block has one Sylow conjugate. -/
theorem MinimalBlockSetup.alternating_five_single_of_second
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hsecond : ∀ A : Subgroup Janko4.InvolutionCentralizers.Second.ambientCentralizer,
      IsAlternatingBlock A 5 → Nat.card ((blockU A).map A.subtype) = 16 →
      ∀ S : Sylow 2 Janko4.InvolutionCentralizers.Second.ambientCentralizer,
        A ∉ ChapterA.Section03.localCComponents S) : d.L0 = d.block := by
  by_contra hpair
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c⟩ := d.alternating_pair_configuration hG T hST.le hpair hA M₀ hSM hMT hi
  obtain ⟨K,hK,hLK,hNK⟩ := c.phi_ordinary_component hG T hM hTM hu hST.le hSM hMT hi
  obtain ⟨n,hn,hm⟩ := c.ordinary_overcomponent_remaining hG T hM hTM hu hST.le hSM hMT hi K hK hLK hNK
  rcases hn with rfl | rfl
  · exact c.j4_overcomponent_false_of_second hG T hM hTM hu hST.le hSM hMT hi K hK hLK hNK hsecond hm
  · exact c.held_overcomponent_false hG T hM hTM hu hST.le hSM hMT hi K hK hLK hNK hm
end CFSG.Quasithin.Chapter2

