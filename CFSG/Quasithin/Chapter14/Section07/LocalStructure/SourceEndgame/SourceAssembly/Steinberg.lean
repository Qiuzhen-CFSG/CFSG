module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.Thompson
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Count
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Commutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus.Application
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.ParabolicSupport

/-!
# Source72: the original Steinberg section and two-core

The actual three-factor flag on S/V recognizes the Steinberg module. Its
parabolic generation puts S in L₁ only after that recognition. The original
cubic torus then constructs the involution excluding the double cover,
giving S=O₂(L)=[O₂(L),L]. The already constructed source generation gives
U₀=V₁ and all three special-group layers. The final application constructs
all of these premises from one original source70 rechoice.

Source: Aschbacher–Smith,14.7.71–72,printed pp.1075–1076.
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

/-- All four conclusions of72 on the original section and subgroups. -/
structure Conclusion72 (d : Data T L V F W) : Prop where
  core : S F L = L.pCoreIn 2
  core_generation : ⁅L.pCoreIn 2,L⁆ = L.pCoreIn 2
  steinberg : Nonempty (SteinbergCoordinates d)
  fixed_kernel : d.U₀ = F.Vi 1
  center_eq : (center (S F L)).map (S F L).subtype = V
  frattini_eq : (frattini (S F L)).map (S F L).subtype = V
  derived_eq : ⁅S F L,S F L⁆ = V
  core_commutator : ⁅Q T L,L⁆ = S F L

/-- Construct recognition, parabolic support, involution and core identity. -/
theorem finish_steinberg_and_core (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (actors : MarkedSpans.LocalActors d)
    (gen : SourceGeneration.Conclusion d)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (selection : c.RankSelection) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) : Conclusion72 d := by
  have hTL := d.natural.sylow_normalizes structural
  have hSQ : S F L ≤ Q T L := ChiefFactors.QKPlacement.S_le_Q d structural e.separation
  let := quotient_normal gen.frattini_eq
  let := quotient_elementary hSQ gen.frattini_eq
  let a := quotientAction d hTL gen.core_commutator.le
  obtain ⟨X,aX,mX,hs⟩ := CriticalIntersections.exists_sourceDuality d e.sectionCentralizer
  let := aX
  let := mX
  obtain ⟨duality⟩ := hs
  obtain ⟨b⟩ := ChiefFactors.HAccounting.exists_qKDualCoordinates d e.sectionCentralizer duality hcomm
  have hcount := ChiefFactors.QKPlacement.SourceCompletion.source_71_count d structural c e mark
    gen.fixed_kernel b a
  obtain ⟨s⟩ := ParabolicSteinberg.recognized_of_source_count d a hTL e.separation gen.fixed_kernel hcount
  have h71 : ⁅Q T L,L⁆ ≤ S F L :=
    ChiefFactors.QKPlacement.SourceCompletion.commutator_Q_L_le_S d structural c e mark b
  have hSP := CoreIdentification.SourceInvolution.ParabolicSupport.S_le_parabolic d s
    gen.frattini_eq hSQ hTL
  obtain ⟨hF9,hF9α⟩ := critical_core_commutator_bounds c hcomm
  have invol := CoreIdentification.SourceInvolution.exists_source_involution_of_earlier_cubic
    d c e mark actors duality hcomm gen.fixed_kernel hSP hTL hSQ selection hUH heven hF9 hF9α
  obtain ⟨hcore,hderived⟩ := CoreIdentification.core_and_commutator_of_critical_conjugate
    d s gen.frattini_eq hSQ h71 hTL c.Uα invol
  exact ⟨hcore,hderived,⟨s⟩,gen.fixed_kernel,
    center_eq_of_steinberg d s gen.seed_central gen.derived_eq,gen.frattini_eq,gen.derived_eq,
    (CoreIdentification.S_eq_commutator_Q_L d s gen.frattini_eq hSQ h71).symm⟩

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

/-- All source72 conclusions, with71 placement/count and native Thompson input discharged. -/
theorem source_lemma_14_7_72
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
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) : Conclusion72 d := by
  let d' := LeftChiefFactors.BorelRefinements.upperRemark d structural
  have hc := d'.sectionCentralizer_of_earlier_setup structural uniqueness
  have mark := LeftChiefFactors.BorelRefinements.upperRemark_upperMarking d structural
  have actors := Rechoice.SourceCompletion.localActors_of_source d structural
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
  obtain ⟨s⟩ := hout.steinberg
  have hqL : d'.qL = d.qL := d'.qL_eq_of_natural_eq d rfl
  have steinberg : Nonempty (SteinbergCoordinates d) := ⟨{
    coordinates := s.coordinates
    onto := s.onto
    kernel_eq := s.kernel_eq
    equivariant := by
      intro l a
      have he := s.equivariant l a
      rw [hqL] at he
      exact he }⟩
  exact ⟨hout.core,hout.core_generation,steinberg,hout.fixed_kernel,hout.center_eq,
    hout.frattini_eq,hout.derived_eq,hout.core_commutator⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
