module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion.Outputs
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.Steinberg

/-!
# From the actual source72 conclusions to the source73 roots

The proved Steinberg coordinates are converted to a conjugation section only
after S=O₂(L) has been established. All root-generation, natural-coordinate,
Sylow and cardinality data are then constructed. Escape from the original
normalizer supplies a genuine k outside L₁T. No additional 73 output is an
input; the universal earlier G.1.3 classifier remains with qt-g-01.

Source: Aschbacher–Smith 14.7.73, printed pp.1076–1077.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

include d in
/-- The original K contains an element outside the source point normalizer. -/
theorem exists_root_conjugator
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ∃ k : K F, (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G) := by
  have hTL := d.natural.sylow_normalizes structural
  have hH : ¬ F.H ≤ normalizer (L : Set G) := by
    have hh : F.H ∈ F.Hz L (normalizer (L : Set G)) := by
      rw [d.unique_Hz]
      exact Set.mem_singleton _
    exact hh.2.2
  by_contra hk
  push Not at hk
  have hK : K F ≤ normalizer (L : Set G) := fun x hx =>
    sup_le (((F.Li_le L 1).trans inf_le_left).trans L.le_normalizer) hTL (hk ⟨x,hx⟩)
  exact hH (d.residual_product ▸ sup_le hK hTL)

/-- Apply the original72 outputs, without assuming a section, natural root
coordinates, generation, Sylow placement or any count from73. -/
theorem finish_roots
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : SourceAssembly.Conclusion72 d)
    (recognition : Geometry.NaturalRecognition.{u}) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G)) : Conclusion73 d k := by
  obtain ⟨s⟩ := h72.steinberg
  exact roots_of_source_sections d structural c e mark hcomm h72.core h72.center_eq
    h72.frattini_eq h72.fixed_kernel (s.toSection (h72.core.le.trans (pCoreIn_le 2 L)))
    recognition k hk

/-- A genuine source conjugator and all its root conclusions exist. -/
theorem exists_roots
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : SourceAssembly.Conclusion72 d) (recognition : Geometry.NaturalRecognition.{u}) :
    ∃ k : K F, (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G) ∧ Conclusion73 d k := by
  obtain ⟨k,hk⟩ := exists_root_conjugator d structural
  exact ⟨k,hk,finish_roots d structural c e mark hcomm h72 recognition k hk⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
