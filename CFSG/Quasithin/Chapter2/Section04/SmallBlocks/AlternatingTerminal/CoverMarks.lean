module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Ordinary
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.NormalizerTransfer
/-!
# The faithful block in the literal component quotient

The original block is disjoint from the two-core of the Phi normalizer.
Subnormality places the ordinary component's two-core inside that same core,
so the literal quotient map is injective on the original block. Its deleted
module and order sixteen marking therefore survive unchanged.

Source: Aschbacher–Smith 2.4.25, printed pp.542–543.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.block_component_twoCore_quotient_marks
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
    let A := (L.subgroupOf GI).subgroupOf K
    let q := QuotientGroup.mk' (pCore 2 K)
    IsAlternatingBlock A 5 ∧ Nat.card ((blockU A).map A.subtype) = 16 ∧
      Function.Injective (q.comp A.subtype) ∧
      IsAlternatingBlock (A.map q) 5 ∧
      Nat.card ((blockU (A.map q)).map (A.map q).subtype) = 16 := by
  intro S L GI K hK hLK A q
  have hLG : L ≤ GI := (c.phi_normalizer_source hG T hM hTM hu hST hSM hMT hi).2.2.2.1.trans
    (Subgroup.centralizer_le_normalizer _)
  let a : A ≃* L := (subgroupOfEquivOfLe hLK).trans (subgroupOfEquivOfLe hLG)
  have hA : IsAlternatingBlock A 5 := RankOne.Solvable.isAlternatingBlock_of_equiv a.symm c.marked₁.block
  have hc : Nat.card ((blockU A).map A.subtype) = 16 := by
    rw [card_map_of_injective A.subtype_injective]
    have hca : Nat.card (blockU A) = Nat.card (blockU L) := by
      rw [←RankOne.Solvable.blockU_map_equiv a, card_map_of_injective a.injective]
    rw [hca, ←card_map_of_injective L.subtype_injective]
    exact c.marked₁.module_card
  let f := q.comp A.subtype
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro l hl
    have hq : (l : K) ∈ pCore 2 K := (QuotientGroup.eq_one_iff _).mp hl
    have hp : (l : GI) ∈ pCore 2 GI := pCoreIn_le_of_subnormal 2 hK.1
      (mem_map_of_mem K.subtype hq)
    have hg : (l : G) ∈ twoCore GI := mem_map_of_mem GI.subtype hp
    have h1 := disjoint_def.mp c.block_disjoint_phi_core l.property hg
    exact mem_bot.mpr (Subtype.ext (Subtype.ext (Subtype.ext h1)))
  have hrange : f.range = A.map q := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  let e : A ≃* A.map q := (MonoidHom.ofInjective hfi).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨hA,hc,hfi,RankOne.Solvable.isAlternatingBlock_of_equiv e hA,?_⟩
  rw [card_map_of_injective (A.map q).subtype_injective]
  rw [←RankOne.Solvable.blockU_map_equiv e, card_map_of_injective e.injective]
  rw [←card_map_of_injective A.subtype_injective]
  exact hc
end CFSG.Quasithin.Chapter2
