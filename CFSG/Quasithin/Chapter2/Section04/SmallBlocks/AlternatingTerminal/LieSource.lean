module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.SourceTransfers
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LieRows
/-! The invariant native rank-two escape is lifted through the actual component
two-core and the original SI action. This is the literal paired-source consumer
for all rank-two rows, including the two exceptional central covers.
Source: Aschbacher–Smith 2.4.25, printed p.543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}
theorem AlternatingPairSourceSetup.rank_two_quotient_overcomponent_false
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
    ∀ {D : Type*} [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D],
    Chapter1.Section02.LocalModels.RankTwoTheoremC D →
    Nonempty ((K ⧸ pCore 2 K) ≃* D) → False := by
  intro S L GI K hK hLK hNK D _ _ _ _ hm he
  exact c.invariant_quotient_overcomponent_false hG T hM hTM hu hST hSM hMT hi
    K hK hLK hNK (AlternatingTerminal.rank_two_invariant_obstruction hm) he
end CFSG.Quasithin.Chapter2
