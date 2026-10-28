module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.TypeRu
public import CFSG.Quasithin.ChapterJ.Section01.SourceRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs

/-!
# Rudvalis from the original local source inputs

Choose one critical path and its permitted rechoice. The already constructed
fixed-component, fusion and chief-factor arguments give the generation
identities. The actual Steinberg section, root quotient and local collapse
then construct both Ru records and the concrete Rudvalis isomorphism.

This conditional application retains Data and the independent structural,
faithful-family and A₅ module inputs at the original group and Sylow subgroup.
It does not construct Data. Their earlier-source producers and final original
14.7.75 discharge remain with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.63–75, pp.1068–1078, and J.1.1.
-/
public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section03.SourceCompletion
open SteinbergRecognition SteinbergRecognition.ModuleRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (five : OriginalAlternatingFiveModules1332At T L)
include d structural faithful five

/-- All 70–75 geometry and recognition premises are constructed from the
original local inputs. No universal structural or module theorem is used. -/
theorem source_typeRu_from_original_modules_at : ChapterJ.IsTypeRu G := by
  let d' := LeftChiefFactors.BorelRefinements.upperRemark_at d structural
  have hc := d'.sectionCentralizer_from_flag
  have mark := LeftChiefFactors.BorelRefinements.upperRemark_upperMarking_at d structural
  have actors := Rechoice.SourceCompletion.localActors_of_source_at d structural
  have hcomm := d'.U_core_commutator_eq_point_of_original_modules_at five
  obtain ⟨c,selection⟩ := d'.exists_selected_criticalPath_from_original_modules_at structural five
  have earlier := d'.source_earlierImages_at structural c
    (d'.source_Q_star_eq_Ri_at structural hcomm.le
      (d'.plane_noncentrality_of_original_modules_at five))
    (d'.source_Ri_star_sylow_at structural)
  have h69 := d'.order_two_from_original_modules_at structural faithful five c selection
  have hUH := d'.source_reciprocal_placement c
  have heven := d'.source_reciprocal_even_at structural c earlier
  obtain ⟨h70,gen⟩ := rechoice_and_generation_from_original_modules_at d' structural faithful five c selection
  obtain ⟨n,hp,hrank,hi,hV,hU₀,hb,hconj⟩ := h70
  let e : ChiefFactors.Earlier d' (c.reselect n) := {
    separation := Rechoice.SourceCompletion.moduleSeparation d'
    sectionCentralizer := hc
    images := c.reselect_earlierImages earlier n
    point := hp
    image_order := (c.reselect_star_card earlier n).trans h69
    intersection := hi
    commutator_seed := hV
    commutator_fixed := hU₀
    distance := hb
    conjugate := hconj }
  have hout := finish_steinberg_and_core_at d' structural (c.reselect n) e mark actors gen hcomm
    (reselect_rankSelection d' c earlier selection n)
    (reselect_reciprocal_placement d' c n hUH)
    (reselect_reciprocal_even d' c n hUH heven)
  exact (typeRu_of_source72_at d' structural (c.reselect n) e mark hcomm hout
    RootRecognition.Geometry.SourceCompletion.naturalRecognition).2

/-- The literal Rudvalis isomorphism, conditional only on Data and the
independent source inputs at its original G,T,L. -/
theorem source_rudvalis_from_original_modules_at : Nonempty (G ≃* Rudvalis.Model) :=
  ChapterJ.theorem_J_1_1 (source_typeRu_from_original_modules_at d structural faithful five)

/-- This Rudvalis branch feeds the full Theorem-D model conclusion. -/
theorem source_theoremDModel_from_original_modules_at : ClassificationModels.IsTheoremDModel G := by
  exact .exceptional (.sporadic .ru (by simp)
    (source_rudvalis_from_original_modules_at d structural faithful five))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
