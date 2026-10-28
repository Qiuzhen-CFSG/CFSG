module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.CoverMarks
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.QuotientNormalizerTransfer
/-!
# The actual ambient component image and its faithful quotient

The image of the ordinary component in the original ambient group contains
the original deleted A₅ block. Its two-core is contained in the two-core of
the Phi normalizer, so the quotient preserves the block and its order sixteen
module. These are the literal maps used by the escaping-overgroup consumers.

Source: Aschbacher–Smith 2.4.25, printed p.543.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.block_image_component_twoCore_quotient_marks
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
    let E := K.map GI.subtype
    let A := L.subgroupOf E
    let q := QuotientGroup.mk' (pCore 2 E)
    L ≤ E ∧ IsAlternatingBlock A 5 ∧ Nat.card ((blockU A).map A.subtype) = 16 ∧
      Function.Injective (q.comp A.subtype) ∧
      IsAlternatingBlock (A.map q) 5 ∧
      Nat.card ((blockU (A.map q)).map (A.map q).subtype) = 16 := by
  intro S L GI K hK hLK E A q
  have hLG : L ≤ GI := (c.phi_normalizer_source hG T hM hTM hu hST hSM hMT hi).2.2.2.1.trans
    (Subgroup.centralizer_le_normalizer _)
  have hLE : L ≤ E := by
    intro l hl
    exact ⟨⟨l,hLG hl⟩,hLK hl,rfl⟩
  let a : A ≃* L := subgroupOfEquivOfLe hLE
  have hA : IsAlternatingBlock A 5 := RankOne.Solvable.isAlternatingBlock_of_equiv a.symm c.marked₁.block
  have hc : Nat.card ((blockU A).map A.subtype) = 16 := by
    rw [card_map_of_injective A.subtype_injective]
    have hca : Nat.card (blockU A) = Nat.card (blockU L) := by
      rw [←RankOne.Solvable.blockU_map_equiv a,card_map_of_injective a.injective]
    rw [hca,←card_map_of_injective L.subtype_injective]
    exact c.marked₁.module_card
  let f : K ≃* E := K.equivMapOfInjective GI.subtype GI.subtype_injective
  have hcore : (pCore 2 E).map E.subtype ≤ twoCore GI := by
    rw [←pCore_map_iso 2 f,map_map]
    change (pCore 2 K).map (GI.subtype.comp K.subtype) ≤ _
    rw [←map_map]
    exact map_mono (pCoreIn_le_of_subnormal 2 hK.1)
  let g := q.comp A.subtype
  have hgi : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    apply eq_bot_iff.mpr
    intro l hl
    have hq : (l : E) ∈ pCore 2 E := (QuotientGroup.eq_one_iff _).mp hl
    have hg : (l : G) ∈ twoCore GI := hcore (mem_map_of_mem E.subtype hq)
    have h1 := disjoint_def.mp c.block_disjoint_phi_core l.property hg
    exact mem_bot.mpr (Subtype.ext (Subtype.ext h1))
  have hrange : g.range = A.map q := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  let e : A ≃* A.map q := (MonoidHom.ofInjective hgi).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨hLE,hA,hc,hgi,RankOne.Solvable.isAlternatingBlock_of_equiv e hA,?_⟩
  rw [card_map_of_injective (A.map q).subtype_injective,
    ←RankOne.Solvable.blockU_map_equiv e,card_map_of_injective e.injective,
    ←card_map_of_injective A.subtype_injective]
  exact hc
end CFSG.Quasithin.Chapter2
