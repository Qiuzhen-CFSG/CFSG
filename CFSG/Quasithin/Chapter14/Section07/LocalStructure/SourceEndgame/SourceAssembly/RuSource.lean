module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.Ru
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.PlaneNoncentralitySource

/-!
# Source75 Ru hypotheses from the original critical path

One original rechoice constructs the71 data, Steinberg and special-group
structure, root and quotient data, and the full local collapse. The actual
source1332 module classification excludes plane centrality; no commutator,
Thompson, generation, recognition-output or collapse premise is added.
The genuine earlier universal source inputs retain their named producers.
Terminal identification of a group of type Ru is the separate J.1.1 theorem.

Source: Aschbacher–Smith,14.7.70–75,printed pp.1074–1078.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open SteinbergRecognition SteinbergRecognition.ModuleRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
  (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
    ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
  (sourceF : FSource.ClassificationInput KnownSimple.IsKnownSimple.{u})
include structural uniqueness faithful b5 amalgams sourceF

/-- The source75 Ru records from the original earlier critical-path inputs.
All70–74 local conclusion-shaped premises are constructed internally. -/
theorem source_typeRu
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (recognition : RootRecognition.Geometry.NaturalRecognition.{u})
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l)
    (h13 : ∀ n : group F L, SourceGeneration.EarlierThirteen (c.reselect n))
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) : ChapterJ.IsTypeRu G := by
  let d' := LeftChiefFactors.BorelRefinements.upperRemark d structural
  have hc := d'.sectionCentralizer_of_earlier_setup structural uniqueness
  have mark := LeftChiefFactors.BorelRefinements.upperRemark_upperMarking d structural
  have actors := Rechoice.SourceCompletion.localActors_of_source d structural
  have hmove := d'.plane_noncentrality_of_source1332 earlier1332 hc
  have hcomm := d'.U_core_commutator_eq_point_of_plane_moved hc hmove
  obtain ⟨h70,gen⟩ := rechoice_and_generation d' c structural uniqueness faithful b5 amalgams sourceF
    earlier selection h69 hmove h68 hUH heven earlier_conjugacy h13 hcentralizer68
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
  have hout := finish_steinberg_and_core d' structural (c.reselect n) e mark actors gen hcomm
    (reselect_rankSelection d' c earlier selection n)
    (reselect_reciprocal_placement d' c n hUH)
    (reselect_reciprocal_even d' c n hUH heven)
  exact (typeRu_of_source72 d' structural uniqueness (c.reselect n) e mark hcomm hout recognition).2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
