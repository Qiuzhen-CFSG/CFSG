module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.Ru
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Collapse

/-!
# The original 14.7.75 TypeRu assembly at the fixed group

Apply the Steinberg and root conclusions to the local collapse, then
construct the two Ru records with their original centralizers and maps.
Only the structural input at the original G,T is used. Earlier-source
construction and final discharge remain with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.71–75, printed pp.1075–1078.
-/
public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Construct the full preceding-source record required by74. -/
def collapsePrior_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (h72 : Conclusion72 d) (k : K F)
    (h73 : RootRecognition.SourceCompletion.Conclusion73 d k) : LocalCollapse.Prior d := by
  let s := Classical.choice h72.steinberg
  refine {
    separation := Rechoice.SourceCompletion.moduleSeparation d
    sylow_normalizes := d.natural.sylow_normalizes_at structural
    unique_overgroup := (d.natural.maximal_unique_at structural).2
    centralizer_LT := d.natural.centralizer_LT_at structural
    core := h72.core
    steinberg := s.toSection (h72.core.le.trans (pCoreIn_le 2 L))
    center := h72.center_eq
    frattini := h72.frattini_eq
    derived := ?_
    commutator := h72.core_commutator
    point_kernel := h72.fixed_kernel
    parabolic_core := h73.parabolic.symm
    parabolic_sylow := ?_
    sylow_index := h73.index
    core_order := h73.card }
  · rw [map_subtype_commutator]
    exact h72.derived_eq
  · obtain ⟨R,hR⟩ := h73.sylow_witness
    exact ⟨R,hR.trans h73.parabolic.symm⟩

/-- The actual72 result produces full74 and the source75 Ru hypotheses. -/
theorem typeRu_of_source72_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : Conclusion72 d) (recognition : RootRecognition.Geometry.NaturalRecognition.{u}) :
    LocalCollapse.SourceCompletion.Conclusion74 d ∧ ChapterJ.IsTypeRu G := by
  obtain ⟨k,hk,h73⟩ := RootRecognition.SourceCompletion.exists_roots_at d structural c e mark
    hcomm h72 recognition
  let a := collapsePrior_at d structural h72 k h73
  have h74 := LocalCollapse.SourceCompletion.source_lemma_14_7_74_at d structural a c e mark hcomm
  obtain ⟨s⟩ := h72.steinberg
  have hs := s.toSection (h72.core.le.trans (pCoreIn_le 2 L))
  have hder : (commutator (L.pCoreIn 2)).map (L.pCoreIn 2).subtype = V := by
    rw [map_subtype_commutator, ← h72.core]
    exact h72.derived_eq
  have hsection : BinaryConjugationSection L (L.pCoreIn 2) V (BinaryLinearThree.S.comp d.qL) := by
    rw [← h72.core]
    exact hs
  obtain ⟨ru1⟩ := source_ruOne_of_steinberg d a.separation
    (a.sylow_normalizes.trans h74.self_normalizing.le)
    (by rw [← h72.core]; exact h72.center_eq)
    (by rw [← h72.core]; exact h72.frattini_eq)
    hder BinaryLinearThree.S hsection (Representation.Equiv.refl _)
  obtain ⟨ru2⟩ := RootRecognition.SourceCompletion.ruTwo_of_roots d k h73 h72.core
    h72.frattini_eq a.sylow_normalizes h72.fixed_kernel h74.sylow_center h74.core_eq
  exact ⟨h74,⟨⟨L,V,T,ru1,ru2⟩⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
