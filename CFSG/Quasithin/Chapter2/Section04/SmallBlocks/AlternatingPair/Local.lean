module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Base
public import CFSG.Quasithin.Chapter2.Section04.BlockNormality.ChiZeroEmbedding
public import Theory.GroupTheory.SylowNormalSupplementRecognition
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPersistence

/-! The genuine selected A₅ block remains a local C-component at its
index-two Sylow stabilizer. Source 2.4.25, printed p.542. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem alternating_not_three {K : Subgroup G} (h : IsAlternatingBlock K 5) :
    ¬ IsAlternatingBlock K 3 := by
  intro h3
  obtain ⟨e5⟩ := h.2.2.quotient_iso
  obtain ⟨e3⟩ := h3.2.2.quotient_iso
  have hc := Nat.card_congr (e5.symm.trans e3).toEquiv
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  have hthree : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  rw [h5,hthree] at hc
  norm_num at hc

variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.stabilizer_local_component
    (c : AlternatingPairSourceSetup d M₀)
    (hQ : twoCore d.H ≤ ((d.S : Subgroup d.H).map d.H.subtype ⊓
      normalizer (d.block.map d.H.subtype : Set G))) :
    d.block.map d.H.subtype ∈ Chapter1.L G
      ((d.S : Subgroup d.H).map d.H.subtype ⊓
        normalizer (d.block.map d.H.subtype : Set G)) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := S ⊓ normalizer (L : Set G)
  let Y := L ⊔ R
  let C := L.subgroupOf Y
  let RY := R.subgroupOf Y
  have hYH : Y ≤ d.H := sup_le (map_subtype_le _) (inf_le_left.trans (map_subtype_le _))
  have hRp : IsPGroup 2 R := c.marked₁.twoGroup.to_le inf_le_left
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (show Y ≤ normalizer (L : Set G) from sup_le L.le_normalizer inf_le_right)
  let e : L ≃* C := (subgroupOfEquivOfLe (show L ≤ Y from le_sup_left)).symm
  let PL : Sylow 2 C := c.marked₁.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPL : (PL : Subgroup C).map C.subtype ≤ RY := by
    rintro y ⟨p,hp,rfl⟩
    obtain ⟨l,hl,he⟩ := hp
    have hlS : (l : G) ∈ S := (c.marked₁.sylow_image ▸ mem_map_of_mem L.subtype hl).1
    change (p : Y) ∈ RY
    rw [←he]
    exact ⟨hlS,L.le_normalizer l.property⟩
  obtain ⟨P,hP⟩ := exists_sylow_eq_of_normal_supplement C RY hRp.comap_subtype
    (codisjoint_subgroupOf_sup L R).eq_top PL hPL
  have hSyl : Chapter1.IsSylowIn 2 R Y := ⟨P, by rw [hP]; exact map_subgroupOf_eq_of_le le_sup_right⟩
  have hHa : IsAlternatingBlock d.block 5 := RankOne.Solvable.isAlternatingBlock_of_equiv
    (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm c.marked₁.block
  have hBc : (L.subgroupOf d.H).IsCComponent := by
    have he : L.subgroupOf d.H = d.block := comap_map_eq_self_of_injective d.H.subtype_injective _
    exact he ▸ d.block_isCComponent_of_not_three (alternating_not_three hHa)
  have hcore : twoCore d.H ≤ twoCore Y := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 d.H) (hQ.trans le_sup_right)
    (hYH.trans (le_normalizer_twoCore d.H))
  have hY : Y ∈ Chapter1.H G := by
    intro he
    have hH : twoCore d.H ≠ ⊥ :=
      (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
    exact hH (le_bot_iff.mp (hcore.trans he.le))
  exact Chapter1.mem_L_of_cComponent hY hSyl le_sup_left (hBc.subgroupOf_of_le le_sup_left hYH)

/-- The starred persistence claim on the literal stabilizer of the selected block. -/
theorem AlternatingPairSourceSetup.stabilizer_persistence
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (X : Subgroup G) (hX : X ∈ Chapter1.He G) (P : Sylow 2 X)
    (hRP : (d.S : Subgroup d.H).map d.H.subtype ⊓
      normalizer (d.block.map d.H.subtype : Set G) ≤ (P : Subgroup X).map X.subtype)
    (hgen : X = d.block.map d.H.subtype ⊔ (P : Subgroup X).map X.subtype) :
    ((d.block.map d.H.subtype).subgroupOf X).IsCComponent := by
  obtain ⟨hhalf,_,hQ,hbeta⟩ := c.stabilizer_base hG T hM hTM hu hST hSM hMT hi
  exact d.alternating_persistence hG T hTM hu inf_le_left hhalf hbeta
    (c.stabilizer_local_component hQ) hX P hRP hgen

end CFSG.Quasithin.Chapter2
