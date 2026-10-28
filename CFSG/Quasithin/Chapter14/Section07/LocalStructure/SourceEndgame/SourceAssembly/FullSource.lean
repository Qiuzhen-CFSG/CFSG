module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.RuRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion.FullSource

/-!
# The original TypeRu assembly with the complete source F.6 boundary

The actual dihedral PSL₂ and square-field alternatives are compared in the entire critical
rechoice and source 70–75 chain. The native Thompson and G.1.3 results are
applied internally, and genuine A/C supplies the original uniqueness theorem.
The source Data, CriticalPath, quotient maps and one selected rechoice are
retained throughout. The other named earlier source producers remain explicit.

Source: Aschbacher–Smith, F.6.18 and 14.7.70–75, printed pp.309–310,1074–1078.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt
open CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open SteinbergRecognition
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
  (sourceF : FSource.SourceClassificationInput KnownSimple.IsKnownSimple.{u})
include structural uniqueness faithful b5 amalgams sourceF

/-- The actual70 producer discharges all selected-path generation premises. -/
theorem rechoice_and_generation
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G))
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l)
    (h13 : ∀ n : group F L, SourceGeneration.EarlierThirteen (c.reselect n))
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    Statement c d ∧ SourceGeneration.Conclusion d := by
  let thompson := Chapter14.Section03.ThompsonSource.earlierThompsonNormality structural
  have separation := Rechoice.SourceCompletion.moduleSeparation d
  have hcomm := d.U_core_commutator_eq_point_of_plane_moved
    (d.sectionCentralizer_of_earlier_setup structural uniqueness) hmove
  let d' := LeftChiefFactors.BorelRefinements.upperRemark d structural
  obtain ⟨n, _, hpoint, hp, hrank, hi, hV, hU₀, hb, hconj⟩ :=
    Rechoice.SourceCompletion.FullSource.source_rechoice_with_point d c structural uniqueness thompson
      faithful b5 amalgams sourceF earlier selection h69 separation hcomm h68 hUH heven
      earlier_conjugacy
  have hout := generation_of_selected_rechoice d' structural c n earlier separation
    (d'.sectionCentralizer_of_earlier_setup structural uniqueness)
    (LeftChiefFactors.BorelRefinements.upperRemark_upperMarking d structural)
    (Rechoice.SourceCompletion.localActors_of_source d structural)
    h69 hp hrank hi hV hU₀ hb hconj (h13 n) hpoint hcentralizer68
  refine ⟨⟨n, hp, hrank, hi, hV, hU₀, hb, hconj⟩, ?_⟩
  exact ⟨hout.original_commutator, hout.span_central, hout.span_intersection,
    hout.residual_commutator, hout.actor_commutator, hout.span_join, hout.fixed_kernel,
    hout.fixed_span, hout.seed_central, hout.frattini_eq, hout.derived_eq,
    hout.core_commutator, hout.seed_central_in_Q⟩


open SteinbergRecognition.ModuleRecognition

/-- The source75 Ru records from the original earlier critical-path inputs.
All70–74 local conclusion-shaped premises are constructed internally. -/
theorem source_typeRu
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
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
  exact (typeRu_of_source72 d' structural uniqueness (c.reselect n) e mark hcomm hout RootRecognition.Geometry.SourceCompletion.naturalRecognition).2


omit uniqueness in
/-- The source75 Ru records from the original earlier critical-path inputs.
All70–74 local conclusion-shaped premises are constructed internally. -/
theorem source_typeRu_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (earlier1332 : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l)
    (h13 : ∀ n : group F L, SourceGeneration.EarlierThirteen (c.reselect n))
    (hcentralizer68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) : ChapterJ.IsTypeRu G := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S K hK
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC hA hC hX S hK
  exact source_typeRu d c structural uniqueness faithful b5 amalgams sourceF earlier selection
    h69 earlier1332 h68 hUH heven earlier_conjugacy h13 hcentralizer68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
