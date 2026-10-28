module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion

/-!
# The original Ru data from the completed local endgame

The72 Steinberg section and73 parabolic outputs construct every field of
LocalCollapse.Prior. The actual74 proof then gives M=L and Q_H=O₂(K).
The original qL and qH supply the two Ru records, with the original V, U,
Sylow group and their literal centralizers and quotient maps retained.

Source: Aschbacher–Smith,14.7.72–75,printed pp.1076–1078.
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
def collapsePrior
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (h72 : Conclusion72 d) (k : K F)
    (h73 : RootRecognition.SourceCompletion.Conclusion73 d k) : LocalCollapse.Prior d := by
  let s := Classical.choice h72.steinberg
  refine {
    separation := Rechoice.SourceCompletion.moduleSeparation d
    sylow_normalizes := d.natural.sylow_normalizes structural
    unique_overgroup := (d.natural.maximal_unique structural uniqueness).2
    centralizer_LT := d.natural.centralizer_LT structural
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
theorem typeRu_of_source72
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : Conclusion72 d) (recognition : RootRecognition.Geometry.NaturalRecognition.{u}) :
    LocalCollapse.SourceCompletion.Conclusion74 d ∧ ChapterJ.IsTypeRu G := by
  obtain ⟨k,hk,h73⟩ := RootRecognition.SourceCompletion.exists_roots d structural c e mark
    hcomm h72 recognition
  let a := collapsePrior d structural uniqueness h72 k h73
  have h74 := LocalCollapse.SourceCompletion.source_lemma_14_7_74 d structural a c e mark hcomm
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
