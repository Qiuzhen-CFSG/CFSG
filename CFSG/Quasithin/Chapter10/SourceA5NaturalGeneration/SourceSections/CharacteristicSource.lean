module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.CharacteristicPair
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.NaturalBlockAlternative
/-!
# One characteristic pair on the actual original local embeddings

The two local groups are retained in their intrinsic ambient subgroups.
Their actual inclusions agree on the original Baumann subgroup, so one
universal characteristic pair applies to both. The vanishing fixed centers
eliminate both central alternatives and original maximal-overgroup uniqueness
eliminates simultaneous normality. The resulting block belongs to the original
L or the SAME selected H-star component K. In the K alternative its natural
type is retained; no new conjugation module or ambient local-class transport
is assumed.

Source: Aschbacher–Smith C.1.18–19 and10.2.3(4), pp.126–127 and746–747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open ChapterB Chapter3.Section02 ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
/-- One of the actual selected local groups has the C.1.18 block alternative. -/
theorem source_hstar_selected_block_alternative_of_embeddings {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZL : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hZH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (NL NH : Type u) [Group NL] [Finite NL] [Group NH] [Finite NH]
    (iL : NL →* G) (iH : NH →* G)
    (bL : baumann (T : Subgroup G) →* NL)
    (bH : baumann (T : Subgroup G) →* NH)
    (hbL : iL.comp bL = (baumann (T : Subgroup G)).subtype)
    (hbH : iH.comp bH = (baumann (T : Subgroup G)).subtype)
    (hLgen : localOrbit T L ≤ iL.range ⊔ (T : Subgroup G))
    (hHgen : H ≤ iH.range ⊔ (T : Subgroup G))
    (hlocalL : InLocalClass bL) (hlocalH : InLocalClass bH) :
    BlockAlternative NL ∨ BlockAlternative NH := by
  have hTne : (T : Subgroup G) ≠ ⊥ := fun he =>
    D.seed_ne_bot (bot_unique (D.seed_le_sylow.trans he.le))
  obtain ⟨P,hP,hfirst⟩ := FixedPair.exists_uniform_pair.{u,u} T hTne
  let B := baumann (T : Subgroup G)
  let C₁ := FixedPair.firstSeed T P
  let C₂ := P.second.map B.subtype
  have hC₁Z : C₁ ≤ omegaOneCenterAmbient (T : Subgroup G) := inf_le_left
  have hTC₁ : (T : Subgroup G) ≤ centralizer (C₁ : Set G) := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp (hC₁Z hz)).2.2 t ht).symm
  have hC₂T : C₂ ≤ (T : Subgroup G) := (map_subtype_le P.second).trans inf_le_left
  let : P.second.Characteristic := P.second_characteristic
  have hTC₂ : (T : Subgroup G) ≤ normalizer (C₂ : Set G) :=
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image _ P.second)
  have hC₂ne : C₂ ≠ ⊥ := fun he => P.second_ne_bot
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have first {N : Type u} [Group N] (i : N →* G)
      (b : B →* N) (hi : i.comp b=B.subtype)
      (hc : P.first.map b ≤ center N) :
      i.range ≤ centralizer (C₁ : Set G) := by
    rintro _ ⟨n,rfl⟩ z hz
    obtain ⟨a,ha,rfl⟩ := hz.2
    have he := congrArg i (mem_center_iff.mp (hc (mem_map_of_mem b ha)) n)
    have hea : i (b a) = (a:G) := DFunLike.congr_fun hi a
    change (a:G) * i n = i n * (a:G)
    simpa only [map_mul,hea] using he.symm
  have second {N : Type u} [Group N] (i : N →* G)
      (b : B →* N) (hi : i.comp b=B.subtype)
      (hn : (P.second.map b).Normal) : i.range ≤ normalizer (C₂ : Set G) := by
    let := hn
    have h := (P.second.map b).le_normalizer_map i
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,map_map,hi] at h
    exact h
  have hln : iL.range ≤ normalizer (C₂ : Set G) ∨ BlockAlternative NL := by
    rcases hP NL bL hlocalL with hc | hn | hb
    · have hz : C₁ ≤ centralizer (localOrbit T L : Set G) :=
        le_centralizer_iff.mpr (hLgen.trans (sup_le (first iL bL hbL hc) hTC₁))
      exact (hfirst (bot_unique ((le_inf hC₁Z hz).trans hZL.le))).elim
    · exact Or.inl (second iL bL hbL hn)
    · exact Or.inr hb
  rcases hln with hnL | hb
  · rcases hP NH bH hlocalH with hc | hn | hb
    · have hz : C₁ ≤ centralizer (H : Set G) :=
        le_centralizer_iff.mpr (hHgen.trans (sup_le (first iH bH hbH hc) hTC₁))
      exact (hfirst (bot_unique ((le_inf hC₁Z hz).trans hZH.le))).elim
    · have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
        D.simpleQTKE T D.maximal
      have hN : normalizer (C₂ : Set G) ≤ D.maximalLocal :=
        normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness hu).2.2
          (T.isPGroup'.to_le hC₂T) hC₂ne
          (sup_le (hLgen.trans (sup_le hnL hTC₂)) hTC₂)
      exact (hH.1.2 (hHgen.trans ((sup_le (second iH bH hbH hn) hTC₂).trans hN))).elim
    · exact Or.inr hb
  · exact Or.inl hb

private theorem component_twoPerfect {A : Type*} [Group A] [Finite A]
    {K : Subgroup A} (hK : K.IsCComponent) : IsPPerfect 2 K := by
  let := hK.perfect
  intro Q hQ hp
  let := hQ
  let : Group.IsNilpotent (K ⧸ Q) := hp.isNilpotent
  apply top_unique
  rw [←solvableResidual_eq_top (G := K)]
  exact solvableResidual_le_of_solvable_quotient Q

variable {F : Type*} [Field F] [CharP F 2]
local instance characteristicSourceAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
set_option backward.isDefEq.respectTransparency false in
theorem source_hstar_one_block_of_intrinsic_localClass
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F=4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G)=⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hBK : baumann (T.subtype hH.1.1.2 : Subgroup H) ≤ normalizer (K : Set H))
    (hlocal : InLocalClass (inclusion (show baumann (T.subtype hH.1.1.2 : Subgroup H) ≤
      K ⊔ baumann (T.subtype hH.1.1.2 : Subgroup H) from le_sup_right)))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H)=⊤) :
    ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨
      (ChapterC.IsBlock K ∧ ∃ m, ChapterC.IsL2EvenBlock K m) := by
  let X := localJoin T L
  let SX := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let A := L.subgroupOf X
  let BX := baumann (SX : Subgroup X)
  let BH := baumann (T.subtype hH.1.1.2 : Subgroup H)
  let NL := A ⊔ BX
  let NH := K ⊔ BH
  let iL := X.subtype.comp NL.subtype
  let iH := H.subtype.comp NH.subtype
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hsource := source_original_component_localClass_of_hstar_natural_four D e hn hH hZH hF f n
  obtain ⟨bL,hbL,hiL⟩ := source_original_common_baumann_embedding_of_hstar_natural_four
    D e hn hH hZH hF f n
  obtain ⟨bH,hbH,hiH⟩ := original_baumann_embedding (T : Subgroup G) H hH.1.1.2
    NH (show BH ≤ NH from le_sup_right) hlocal
  have hLrange : L ≤ iL.range := by
    intro l hl
    exact ⟨⟨⟨l,hLX hl⟩,(le_sup_left : A ≤ NL) hl⟩,rfl⟩
  have hLgen : localOrbit T L ≤ iL.range ⊔ (T : Subgroup G) := by
    have hh : localOrbit T L ≤ L ⊔ (T : Subgroup G) := by
      rw [←componentOrbit_sup]
      exact le_sup_left
    exact hh.trans (sup_le_sup_right hLrange _)
  have hKrange : K.map H.subtype ≤ iH.range := by
    rintro k ⟨a,ha,rfl⟩
    exact ⟨⟨a,(le_sup_left : K ≤ NH) ha⟩,rfl⟩
  have hHgen : H ≤ iH.range ⊔ (T : Subgroup G) := by
    have hTm : (T.subtype hH.1.1.2 : Subgroup H).map H.subtype=(T : Subgroup G) :=
      map_subgroupOf_eq_of_le hH.1.1.2
    have hh := congrArg (map H.subtype) hgen
    rw [Subgroup.map_sup,hTm,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm.le.trans (sup_le_sup_right hKrange _)
  rcases source_hstar_selected_block_alternative_of_embeddings D hH hz hzH
      NL NH iL iH bL bH hiL hiH hLgen hHgen hbL hbH with hb | hb
  · exact Or.inl (SelectedRankOne.selected_component_chi_of_blockAlternative
      SX A hA (component_twoPerfect hA) hsource.2.1 hb).1
  · exact Or.inr (SelectedRankOne.selected_component_natural_of_blockAlternative
      (T.subtype hH.1.1.2) K hK (component_twoPerfect hK) hBK hb)
end CFSG.Quasithin.Chapter10
