module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.SourceOrbits
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Rechoice
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FromRechoice
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.Complete

/-!
# Original 14.7.70 and the 14.7.72 generation identities

The same permitted rechoice supplies the chief-factor centralizer argument
and generation. Its literal source orbit identities prove the earlier
central and Frattini spans; the source 68 centralizer bound excludes the
remaining fixed line. All critical, marking, commutator, fusion, local
Goldschmidt and orbit premises are constructed at the original G,T.
The structural, faithful-family and original A₅ module inputs retain their
existing producers; final 14.7.75 discharge stays with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.70–72, pp.1074–1076.
-/
public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.GenerationModels
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
open SteinbergRecognition SteinbergRecognition.SourceGeneration
open SteinbergRecognition.ModuleRecognition.ParabolicSeed
open Matrix.SpecialLinearGroup
open Representation.SL2FourNatural.PlaneGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Build the earlier-source record from one literal 66–70 path. All marked
module fields, the span containment and Sylow normalization are proved here.
The remaining source13 and68 implications are retained at their exact actors. -/
theorem earlier_of_source_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (actors : LocalActors d)
    (h13 : EarlierThirteen c) (hrank : primeRank 2 d.U₀ ≤ 2)
    (hpoint : F.Vi 1 ≤ ⁅F.U, c.Uα⁆)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Earlier d c := {
  critical := e
  thirteen := h13
  upper_mark := mark
  upper_fixed := upper_fixed d e.sectionCentralizer mark e.separation actors
  point_commutator := hpoint
  irreducible := section_irreducible d e.sectionCentralizer mark e.separation actors
  span_le_Q := (SourceOrbits.U_and_span_le_Q_at d structural).2
  fixed_bound := fixed_card_le_four d hrank
  sylow_normalizes := d.natural.chosen.sylow_normalizes_component
  seed_fixed := seed_fixed d e.sectionCentralizer mark e.separation actors
  centralizer68 := h68 }

/-- The literal 71-centralizer→72-generation consumer, with its earlier marked
module hypotheses discharged instead of being repeated as final assumptions. -/
theorem generation_of_source_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (actors : LocalActors d)
    (h13 : EarlierThirteen c) (hrank : primeRank 2 d.U₀ ≤ 2)
    (hpoint : F.Vi 1 ≤ ⁅F.U, c.Uα⁆)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Conclusion d :=
  generation d c (earlier_of_source_at d structural c e mark actors h13 hrank hpoint h68)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.GenerationModels
public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
open SteinbergRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The parent theorem-70 assembly chooses this one `n` and supplies its
opening commutator at that same path. No universal point-commutator premise
or second rechoice is required. -/
theorem generation_of_selected_rechoice_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (n : Rechoice.group F L)
    (images : c.EarlierImages) (sep : d.ModuleSeparation) (hc : d.SectionCentralizer)
    (mark : UpperMarking d) (actors : LocalActors d)
    (h69 : Nat.card (star F c.Uα) = 2)
    (hplane : (c.reselect n).Zα ≤ F.Vi 2) (hrank : primeRank 2 d.U₀ ≤ 2)
    (hinter : F.U ⊓ (c.reselect n).Uα = d.U₀ ⊔ V)
    (hseed : F.U ⊓ (c.reselect n).Uα = ⁅F.U, (c.reselect n).Uα⁆ ⊔ V)
    (hfixed : F.U ⊓ (c.reselect n).Uα = ⁅F.U, (c.reselect n).Uα⁆ ⊔ d.U₀)
    (hb : c.b = 3) (hconj : ∃ l ∈ L, (c.reselect n).Uα = conjugate F.U l)
    (h13 : SourceGeneration.EarlierThirteen (c.reselect n))
    (hpoint : F.Vi 1 ≤ ⁅F.U, (c.reselect n).Uα⁆)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    SourceGeneration.Conclusion d := by
  let e : ChiefFactors.Earlier d (c.reselect n) := {
    separation := sep
    sectionCentralizer := hc
    images := c.reselect_earlierImages images n
    point := hplane
    image_order := (c.reselect_star_card images n).trans h69
    intersection := hinter
    commutator_seed := hseed
    commutator_fixed := hfixed
    distance := hb
    conjugate := hconj }
  exact GenerationModels.generation_of_source_at d structural (c.reselect n) e mark actors
    h13 hrank hpoint h68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section03.SourceCompletion
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open SteinbergRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (five : OriginalAlternatingFiveModules1332At T L)
include d structural faithful five

omit five in
/-- One permitted rechoice feeds the actual generation argument with its
point-commutator witness and the original orbit identities. -/
theorem rechoice_and_generation_at
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (selection : c.RankSelection) (h69 : Nat.card (star F c.Uα) = 2)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (fusion : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hconj : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l)
    (centralizers : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Statement c d ∧ SourceGeneration.Conclusion d := by
  let d' := LeftChiefFactors.BorelRefinements.upperRemark_at d structural
  have sep := Rechoice.SourceCompletion.moduleSeparation d
  obtain ⟨n,_,hpoint,hp,hrank,hi,hV,hU₀,hb,hconj⟩ :=
    Rechoice.SourceCompletion.FullSource.source_rechoice_with_point_at d c structural faithful
      ChapterB.SourceInduction.adequateClassification_knownSimple
      FSource.sourceClassification_knownSimple_complete earlier selection h69 sep hcomm fusion
      (d.source_reciprocal_placement c) (d.source_reciprocal_even_at structural c earlier) hconj
  have hout := generation_of_selected_rechoice_at d' structural c n earlier sep
    d'.sectionCentralizer_from_flag
    (LeftChiefFactors.BorelRefinements.upperRemark_upperMarking_at d structural)
    (Rechoice.SourceCompletion.localActors_of_source_at d structural)
    h69 hp hrank hi hV hU₀ hb hconj
    (SourceOrbits.earlier_thirteen_at d' structural (c.reselect n)) hpoint centralizers
  refine ⟨⟨n,hp,hrank,hi,hV,hU₀,hb,hconj⟩,?_⟩
  exact ⟨hout.original_commutator,hout.span_central,hout.span_intersection,
    hout.residual_commutator,hout.actor_commutator,hout.span_join,hout.fixed_kernel,
    hout.fixed_span,hout.seed_central,hout.frattini_eq,hout.derived_eq,
    hout.core_commutator,hout.seed_central_in_Q⟩

/-- All four source 70 clauses and the literal generation conclusions, using
one selected path and only the independent original G,T source inputs. -/
theorem rechoice_and_generation_from_original_modules_at
    (c : CriticalPath (L := L) F) (selection : c.RankSelection) :
    Statement c d ∧ SourceGeneration.Conclusion d := by
  have hcomm := d.U_core_commutator_eq_point_of_original_modules_at five
  have he := d.source_earlierImages_at structural c
    (d.source_Q_star_eq_Ri_at structural hcomm.le
      (d.plane_noncentrality_of_original_modules_at five))
    (d.source_Ri_star_sylow_at structural)
  have h69 := d.order_two_from_original_modules_at structural faithful five c selection
  obtain ⟨fusion,centralizers⟩ := d.source_lemma_14_7_68_from_original_modules_at structural faithful five
  apply rechoice_and_generation_at d structural faithful c he selection h69 hcomm fusion
  · intro c' hz
    have hb := d.critical_length_three c' hz
    obtain ⟨l,hl,hU⟩ := SourceOrbits.three_conjugate_from_chosen d c' hb
    exact ⟨hb,l⁻¹,L.inv_mem hl,by simpa only [conjugate,inv_inv] using hU⟩
  · intro u hu hne hf
    exact (centralizers u hu hne hf).1

/-- The source selects the path as well, retaining the same path for both conclusions. -/
theorem exists_rechoice_and_generation_from_original_modules_at :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ Statement c d ∧
      SourceGeneration.Conclusion d := by
  obtain ⟨c,hs⟩ := d.exists_selected_criticalPath_from_original_modules_at structural five
  exact ⟨c,hs,rechoice_and_generation_from_original_modules_at d structural faithful five c hs⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
