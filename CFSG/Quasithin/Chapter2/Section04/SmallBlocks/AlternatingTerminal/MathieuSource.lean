module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.SourceTransfers
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.Mathieu
/-! The native elementary-sixteen normalizer of each Mathieu row is pulled back through the literal component two-core quotient. The original SI action preserves the pullback, so starred persistence contradicts its full-Sylow obstruction.
Source: Aschbacher–Smith 2.4.25, printed p.543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}
theorem AlternatingPairSourceSetup.mathieu22_overcomponent_false
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
    Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) → False := by
  intro S L GI K hK hLK hNK hm
  apply c.quotient_normalizer_overcomponent_false hG T hM hTM hu hST hSM hMT hi K hK hLK hNK ?_ hm
  intro B hB hc
  obtain ⟨hN,_,hbad⟩ := AlternatingTerminal.m22_normalizer_obstruction B hB hc
  exact ⟨hN,hbad⟩

theorem AlternatingPairSourceSetup.mathieu23_overcomponent_false
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
    Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) → False := by
  intro S L GI K hK hLK hNK hm
  apply c.quotient_normalizer_overcomponent_false hG T hM hTM hu hST hSM hMT hi K hK hLK hNK ?_ hm
  intro B hB hc
  obtain ⟨hN,_,hbad⟩ := AlternatingTerminal.m23_normalizer_obstruction B hB hc
  exact ⟨hN,hbad⟩

end CFSG.Quasithin.Chapter2
