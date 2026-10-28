module
public import CFSG.Quasithin.ChapterC.Section02.RankOneOffenders
public import Theory.GroupTheory.SylowNormalSupplementRecognition
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.FFClassification
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ThompsonNormalizer
public import Theory.SpecificGroups.SL2.CentralCoreParabolic
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration

/-!
# Actual source geometry in the rank-one B.5 row

The actual star FF classification is applied on its original offender subgroup.
In its rank-one row, ratio-one passage to the moved section identifies every
nonzero maximum-elementary image with a component Sylow. Their join is J(R)*.
The normal component and its two-subgroup supplement then make R* Sylow in
the whole star group; lifting through O₂(LR) makes the original R Sylow.

The already proved source normalizer restriction and the matrix SL₂ Borel
overgroup theorem identify the literal marked intersection as a Borel.
The normal perfect rank-one component also gives minimal parabolicity of LR.
All these conclusions use the same original component, radical and quotient.

This is the rank-one classification branch. Its module data is the actual B.5
row, not a Sylow or Borel assumption. Reconstructing the original block and
handling the other B.5 rows remain source obligations of the C.2.7 assembly.
Source: Aschbacher–Smith C.2.7(3)(a)(i), printed p.146; 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

abbrev StarSourceConclusion {A : Type u} [Group A] (L R : Subgroup A) :=
  ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
    ((starRepresentation L R).comp (offenderSubgroup (starRepresentation L R)).subtype)
    ((starComponent L R).subgroupOf (offenderSubgroup (starRepresentation L R)))

theorem source_rankOne_thompson_sylow
    (h : Input d i j H U K) (L : Subgroup H)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) L)
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H)))
    (hCJ : starComponent L ((sourceRadical d U).subgroupOf H) ≤
      offenderSubgroup (starRepresentation L ((sourceRadical d U).subgroupOf H)))
    (c : StarSourceConclusion L ((sourceRadical d U).subgroupOf H))
    (hratio : quadraticRatio c.sectionData.action = 1)
    (hoff : ∀ B, IsBestOffender c.sectionData.action B →
      ∃ S : Sylow 2 ((starComponent L ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation L ((sourceRadical d U).subgroupOf H)))),
        B = (S : Subgroup _).map
          ((starComponent L ((sourceRadical d U).subgroupOf H)).subgroupOf
            (offenderSubgroup (starRepresentation L ((sourceRadical d U).subgroupOf H)))).subtype) :
    ∃ S : Sylow 2 (starComponent L ((sourceRadical d U).subgroupOf H)),
      (S : Subgroup _).map (starComponent L ((sourceRadical d U).subgroupOf H)).subtype =
        starThompson L ((sourceRadical d U).subgroupOf H) := by
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  have hk : starKernel L R = pCore 2 D :=
    (h.local_module_comparison L hc.normalized hr).2.2.2.2
  have hQR : pCore 2 D ≤ R.subgroupOf D :=
    pCore_le_of_pCore_normalizer_le _ hr.isPGroup hr.2.le
  have hn : ¬ elementaryAbelianMaxJ (R.subgroupOf D) ≤ (starProjection L R).ker := by
    intro hn
    have hh : elementaryAbelianMaxJ (R.subgroupOf D) ≤ pCore 2 D := by
      simpa only [starProjection,QuotientGroup.ker_mk',hk] using hn
    have he := elementaryAbelianMaxJ_eq_of_intermediate _ _ hh hQR
    exact (source_component_core_offenders_of_local_radical h L KnownSimple.IsKnownSimple hc hr).2.1
      he.ge
  have hVQ : omegaCoreModule D ≤ pCore 2 D := by
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  exact ChapterC.thompson_image_sylow_of_bestOffenders
    (omegaCoreModule D) (R.subgroupOf D) hr.isPGroup (hVQ.trans hQR)
    (starProjection L R) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hn
    (starComponent L R)
    (fun _ hA => ChapterC.bestOffender_sylow_of_ratio_one_row
      (starRepresentation L R) (starComponent L R) hCJ c.sectionData hratio hoff hA)



theorem source_local_sylow_of_thompson_sylow
    (h : Input d i j H U K) (L : Subgroup H)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) L)
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H)))
    (S : Sylow 2 (starComponent L ((sourceRadical d U).subgroupOf H)))
    (hS : (S : Subgroup _).map (starComponent L ((sourceRadical d U).subgroupOf H)).subtype =
      starThompson L ((sourceRadical d U).subgroupOf H)) :
    ∃ P : Sylow 2 (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H),
      (P : Subgroup _) = ((sourceRadical d U).subgroupOf H).subgroupOf
        (L ⊔ (sourceRadical d U).subgroupOf H) := by
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let C := starComponent L R
  have hk : starKernel L R = pCore 2 D :=
    (h.local_module_comparison L hc.normalized hr).2.2.2.2
  have hQR : pCore 2 D ≤ R.subgroupOf D :=
    pCore_le_of_pCore_normalizer_le _ hr.isPGroup hr.2.le
  let : (L.subgroupOf D).Normal := hc.local_normal
  let : C.Normal := (inferInstance : (L.subgroupOf D).Normal).map
    (starProjection L R) (QuotientGroup.mk'_surjective _)
  have hgen : C ⊔ starRadical L R = ⊤ := by
    change (L.subgroupOf D).map (starProjection L R) ⊔
      (R.subgroupOf D).map (starProjection L R) = ⊤
    rw [← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hSR : (S : Subgroup _).map C.subtype ≤ starRadical L R := by
    rw [hS]
    exact map_mono (sSup_le fun _ hA => hA.1)
  obtain ⟨T,hT⟩ := exists_sylow_eq_of_normal_supplement C (starRadical L R)
    (hr.isPGroup.map (starProjection L R)) hgen S hSR
  have hker : (starProjection L R).ker = pCore 2 D :=
    (QuotientGroup.ker_mk' _).trans hk
  have hkp : IsPGroup 2 (starProjection L R).ker := hker ▸ pCore_isPGroup
  refine ⟨T.comapOfKerIsPGroup (starProjection L R) hkp ?_, ?_⟩
  · change (T : Subgroup _) ≤ (QuotientGroup.mk' (starKernel L R)).range
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (starKernel L R))]; exact le_top
  · change (T : Subgroup _).comap (starProjection L R) = _
    rw [hT]
    exact comap_map_eq_self (hker ▸ hQR)

private theorem rankOne_normalizer_overgroup
    {A : Type*} [Group A] [Finite A] (F : BinaryField)
    (e : A ≃* SL(2,F.Carrier)) (S : Sylow 2 A)
    (P : Subgroup A) (hP : P ≠ ⊤) (hn : normalizer (S : Set A) ≤ P) :
    P = normalizer (S : Set A) := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hSP : (S' : Subgroup SL(2,F.Carrier)) ≤ P.map e.toMonoidHom :=
    map_mono ((S : Subgroup A).le_normalizer.trans hn)
  have hproper : P.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hP
    have hh := congrArg (comap e.toMonoidHom) he
    simpa only [comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,comap_top] using hh
  have hh := Matrix.SpecialLinearGroup.overgroup_le_sylowNormalizer S' hSP hproper
  have he : normalizer (S' : Set SL(2,F.Carrier)) =
      (normalizer (S : Set A)).map e.toMonoidHom :=
    (map_normalizer_eq_of_bijective _ e.bijective).symm
  rw [he] at hh
  exact le_antisymm ((map_le_map_iff_of_injective e.injective).mp hh) hn



theorem source_star_borel_of_rankOne_sylow
    (h : Input d i j H U K) (L : Subgroup H)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) L)
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H)))
    (F : BinaryField)
    (e : starComponent L ((sourceRadical d U).subgroupOf H) ≃* SL(2,F.Carrier))
    (S : Sylow 2 (starComponent L ((sourceRadical d U).subgroupOf H)))
    (hS : (S : Subgroup _).map (starComponent L ((sourceRadical d U).subgroupOf H)).subtype =
      starThompson L ((sourceRadical d U).subgroupOf H)) :
    IsBorel (starIntersectionIn L ((sourceRadical d U).subgroupOf H) (d.M₁.subgroupOf H)) := by
  let R := (sourceRadical d U).subgroupOf H
  let M := d.M₁.subgroupOf H
  let C := starComponent L R
  let P := starIntersectionIn L R M
  have hm := source_star_thompson_normalizer_of_local_radical h L KnownSimple.IsKnownSimple hc hr
  have hproper : P ≠ ⊤ := by
    intro he
    exact hm.2.not_ge (subgroupOf_eq_top.mp he)
  have hn : normalizer (S : Set C) ≤ P := by
    intro x hx
    have hxN : (x : Star L R) ∈ normalizer (starThompson L R : Set (Star L R)) := by
      rw [←hS]
      exact (S : Subgroup C).le_normalizer_map C.subtype (mem_map.mpr ⟨x,hx,rfl⟩)
    exact hm.1 ⟨x.property,hxN⟩
  exact ⟨S,(rankOne_normalizer_overgroup F e S P hproper hn).symm⟩

theorem source_rankOne_minimalParabolic
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (F : BinaryField)
    (e : starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H) ≃* SL(2,F.Carrier))
    (S : Sylow 2 (starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)))
    (hS : (S : Subgroup _).map
      (starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subtype =
      starThompson (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)) :
    ∃ P : Sylow 2 (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H),
      (P : Subgroup _) = ((sourceRadical d U).subgroupOf H).subgroupOf
        (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H) ∧
      ChapterB.IsMinimalParabolicOver P ⊤ := by
  let L := K₁.subgroupOf H
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let LD := L.subgroupOf D
  have hr := source_local_radical h s hc.normalized
  obtain ⟨P,hP⟩ := source_local_sylow_of_thompson_sylow h L hc hr S hS
  let : LD.Normal := hc.local_normal
  let : Group.IsPerfect LD := (hc.component.subgroupOf le_sup_left).perfect
  let eqL : LD ≃* K₁ := (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).trans
    (subgroupOfEquivOfLe s.component.1)
  let eqQ : (LD ⧸ pCore 2 LD) ≃* SL(2,F.Carrier) :=
    (QuotientGroup.congr _ _ eqL (pCore_map_iso 2 eqL)).trans
      ((SL3Geometry.source_componentStarEquiv h s hc.normalized hr).trans e)
  have hgen : LD ⊔ (P : Subgroup D) = ⊤ := by
    rw [hP,←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  refine ⟨P,hP,?_⟩
  exact Matrix.SpecialLinearGroup.minimal_over_normal_rankOne_core F.Carrier LD P
    hgen eqQ.toMonoidHom eqQ.surjective
    (((MonoidHom.ker_eq_bot_iff eqQ.toMonoidHom).mpr eqQ.injective) ▸ bot_le)



/-- All the Sylow and marked-Borel conclusions in the rank-one B.5 row,
with the same actual section supplied by the source classification. -/
theorem source_selected_rankOne_row_geometry
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (c : StarSourceConclusion (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))
    (F : BinaryField)
    (natural : ActionEquiv
      (c.sectionData.action.comp
        ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
          (offenderSubgroup (starRepresentation (K₁.subgroupOf H)
            ((sourceRadical d U).subgroupOf H)))).subtype) (linearNatural F 2))
    (hratio : quadraticRatio c.sectionData.action = 1)
    (hoff : ∀ B, IsBestOffender c.sectionData.action B →
      ∃ S : Sylow 2 ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)))),
        B = (S : Subgroup _).map
          ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
            (offenderSubgroup (starRepresentation (K₁.subgroupOf H)
              ((sourceRadical d U).subgroupOf H)))).subtype) :
    ∃ S : Sylow 2 (starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)),
      (S : Subgroup _).map
        (starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subtype =
          starThompson (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H) ∧
      IsBorel (starIntersectionIn (K₁.subgroupOf H)
        ((sourceRadical d U).subgroupOf H) (d.M₁.subgroupOf H)) ∧
      ∃ P : Sylow 2 (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H),
        (P : Subgroup _) = ((sourceRadical d U).subgroupOf H).subgroupOf
          (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H) ∧
        ChapterB.IsMinimalParabolicOver P ⊤ := by
  have hr := source_local_radical h s hc.normalized
  have hCJ := (source_selected_ff_classification h s hc).1
  let e := (subgroupOfEquivOfLe hCJ).symm.trans natural.groupEquiv
  obtain ⟨S,hS⟩ := source_rankOne_thompson_sylow h _ hc hr hCJ c hratio hoff
  exact ⟨S,hS,source_star_borel_of_rankOne_sylow h _ hc hr F e S hS,
    source_rankOne_minimalParabolic h s hc F e S hS⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
