module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Quotient
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.CubicStructure
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.CubicContainment

/-! The actual paired A₅ block lies in a unique C-component of G_I,
and its original index-two Sylow stabilizer normalizes that component.
The faithful two-core quotient and surviving cubic from the other block
feed the cubic-centralizer component selection, then solvable-kernel
lifting preserves the literal inclusion. Source2.4.25, printed p542. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.phi_unique_cComponent
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
    ∃! K : Subgroup GI, K.IsCComponent ∧ L.subgroupOf GI ≤ K := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let GI := normalizer (Phi S L : Set G)
  let q := QuotientGroup.mk' (pCore 2 GI)
  let B := (L.subgroupOf GI).map q
  have henv := c.phi_normalizer_source hG T hM hTM hu hST hSM hMT hi
  have hLG : L ≤ GI := henv.2.2.2.1.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨hQ,⟨e⟩,hA,hLayer,b,hb,hbc⟩ := c.phi_quotient_marks hG T hM hTM hu hST hSM hMT hi
  have hlocal := c.stabilizer_local_component
    (c.stabilizer_base hG T hM hTM hu hST hSM hMT hi).2.2.1
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let eg := subgroupOfEquivOfLe hLG
  let : Group.IsPerfect (L.subgroupOf GI) :=
    Group.IsPerfect.ofSurjective (f := eg.symm.toMonoidHom) eg.symm.surjective
  have hBn : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable hlocal
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have hB0 : B ≠ ⊥ := by
    intro he
    apply hBn
    rw [he]
    infer_instance
  obtain ⟨K,hK,hBK⟩ := ChapterA.Section03.perfect_subgroup_le_cComponent_of_cubic_centralizer
    hQ (pCore_quotient_pCore_eq_bot 2) B hB0 hLayer hA.cyclic_three_sylow
    hA.threeResidual_eq_top b hb hbc
  let := pCore_isNilpotent (p := 2) (G := GI)
  apply existsUnique_cComponent_lift_containing (pCore 2 GI)
  refine ⟨K,⟨hK,hBK⟩,?_⟩
  intro J hJ
  exact Chapter1.Section02.IndexTwo.cComponent_unique_over_nonsolvable hBn hJ.1 hK hJ.2 hBK


theorem AlternatingPairSourceSetup.phi_normalized_cComponent
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
    ∃ K : Subgroup GI, K.IsCComponent ∧ L.subgroupOf GI ≤ K ∧
      SI S L ≤ normalizer (K.map GI.subtype : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let GI := normalizer (Phi S L : Set G)
  have henv := c.phi_normalizer_source hG T hM hTM hu hST hSM hMT hi
  have hLG : L ≤ GI := henv.2.2.2.1.trans (Subgroup.centralizer_le_normalizer _)
  have hRG : SI S L ≤ GI :=
    (normalizer_Phi_eq c.marked₁ c.marked₂).ge.trans inf_le_right
  obtain ⟨K,hK,huK⟩ := c.phi_unique_cComponent hG T hM hTM hu hST hSM hMT hi
  have hn : (SI S L).subgroupOf GI ≤ normalizer (L.subgroupOf GI : Set GI) := by
    rw [←subgroupOf_normalizer_eq hLG]
    exact comap_mono inf_le_right
  have hKn := cComponent_le_normalizer_of_unique hK.1 hK.2
    (fun D hD hLD => huK D ⟨hD,hLD⟩) hn
  have hmap := (map_mono (f := GI.subtype) hKn).trans (K.le_normalizer_map GI.subtype)
  rw [map_subgroupOf_eq_of_le hRG] at hmap
  exact ⟨K,hK.1,hK.2,hmap⟩

end CFSG.Quasithin.Chapter2
