module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.LocalMarking
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockModuleContainment
public import Theory.Representation.BinaryPermutation.SevenParabolic.FiveMoved

/-!
# Source coordinates on the full A₇ block module

The marked action identifies the image of L with the alternating group on
five letters. Its moved space is the simple binary five-letter core. The
source module is nonzero, L-invariant and contained in this moved space, so
the two modules coincide. This constructs all fields of the coordinate
contract from source hypotheses.

Source: Aschbacher–Smith, original 4.3.7, printed p.616.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem local_component_sylow_le (c : SourceConfiguration T L) :
    ∃ P : Sylow 2 (c.K.map c.H.subtype),
      (P : Subgroup (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype ≤
        (T : Subgroup G) := by
  obtain ⟨S,hS⟩ := c.sylow
  let : c.K.Normal := c.component_normal
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal c.K
  let e := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  rintro _ ⟨a,⟨k,hk,rfl⟩,rfl⟩
  have hkS : (k : c.H) ∈ (S : Subgroup c.H) := by
    change k ∈ (S : Subgroup c.H).subgroupOf c.K
    rwa [← hP]
  have hh := mem_map_of_mem c.H.subtype hkS
  rw [hS] at hh
  exact hh.1

/-- The original full omega-center module equals the moved five-letter core. -/
theorem SourceConfiguration.alternating_full_module
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (d : BinaryPermutation.SevenParabolic.Ordinary.Chart
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)) (c.K.map c.H.subtype)
      ((ChapterC.blockU (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype))
    (hk : d.actor.ker = pCore 2
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G)) :
    ⁅(ChapterC.blockU (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype,L⁆ =
      Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let f := d.actor
  have ha := d.component_image
  let A := c.K.map c.H.subtype
  let J := A ⊔ ((T : Subgroup G) ⊓ c.H)
  let LA := L.subgroupOf A
  have hAJ : A ≤ J := le_sup_left
  let a := f.comp (inclusion hAJ)
  have hamem (x : A) : a x ∈ alternatingGroup (Fin 7) := by
    rw [← ha]
    exact mem_map_of_mem f x.property
  let q : A →* alternatingGroup (Fin 7) := a.codRestrict _ hamem
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨x,hx,hxb⟩ := ha.ge b.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxb⟩
  have hqker : IsPGroup 2 q.ker := by
    have hfk : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup
    have heq : q.ker = f.ker.comap (inclusion hAJ) := by
      ext x
      change q x = 1 ↔ f (inclusion hAJ x) = 1
      exact Subtype.ext_iff
    rw [heq]
    exact hfk.comap_of_injective _ (inclusion_injective hAJ)
  have hLAker : IsPGroup 2 (q.subgroupMap LA).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hqker.comap_subtype
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hpsl
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := F) hF
  let eLA : LA ≃* L := subgroupOfEquivOfLe c.le_component
  let e : (LA ⧸ pCore 2 LA) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eLA (pCore_map_iso 2 eLA)).trans (eF.trans e5)
  let eimage := alternatingGroup.SevenFiveSection.imageFiveEquiv q LA hLAker e
  obtain ⟨P,hPT⟩ := local_component_sylow_le c
  have hPN : (P : Subgroup A) ≤ normalizer (LA : Set A) := by
    intro p hp l
    exact D.sylow_normalizes_component (hPT (mem_map_of_mem A.subtype hp)) (l : G)
  have hPN' : (P : Subgroup A).map q ≤ normalizer (LA.map q : Set (alternatingGroup (Fin 7))) :=
    (map_mono hPN).trans (LA.le_normalizer_map q)
  have himage : (L.subgroupOf J).map f =
      (LA.map q).map (alternatingGroup (Fin 7)).subtype := by
    ext g
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨q ⟨l,c.le_component hl⟩,⟨⟨l,c.le_component hl⟩,hl,rfl⟩,rfl⟩
    · rintro ⟨b,⟨l,hl,rfl⟩,rfl⟩
      exact ⟨inclusion hAJ l,hl,rfl⟩
  have hU : c.blockLayer = (ChapterC.blockU A).map A.subtype := by
    let eA := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
    have hm := congrArg (map A.subtype) (ChapterC.RankOne.Solvable.blockU_map_equiv eA)
    rw [map_map] at hm
    have he : A.subtype.comp eA.toMonoidHom = c.H.subtype.comp c.K.subtype := by
      ext k
      exact coe_equivMapOfInjective_apply c.K c.H.subtype c.H.subtype_injective k
    rw [he] at hm
    simpa only [SourceConfiguration.blockLayer, map_map] using hm
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  have hn : L ≤ normalizer (Section02.Unitary.fullModule L
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm]
    exact (hs ▸ c.c28.module_commutator).ge
  apply d.five_moved_eq ((map_subtype_le _).trans le_sup_left) L _
    (c.le_component.trans le_sup_left) (LA.map q) eimage (P.mapSurjective hq) hPN' himage
    _ c.c28.module_nontrivial hn
  rw [←hU]
  exact c.fullModule_le_block_commutator hf

/-- All coordinate fields, including the literal full module, follow from
source hypotheses. The factorization and Levi calculation are separate. -/
theorem SourceConfiguration.source_alternating_coordinates
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (ha : ChapterC.IsAlternatingBlock c.K 7) :
    Nonempty (BlockAlternatingCoordinates c) := by
  obtain ⟨d,hk,hr,hl⟩ := c.exists_alternating_marked_chart D hpsl ha
  exact ⟨⟨d,hk,hr,hl,c.alternating_full_module D hpsl hf d hk⟩⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
