module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution

/-!
# Applying the constructed cubic geometry to the critical involution

The actual torus and opposite-plane normalizer discharge the geometry premise
of `exists_source_involution_of_earlier_torus`. All earlier data and the original
critical path are unchanged. The independent parabolic-support premise S≤L₁
remains explicit, as do the earlier reciprocal F.9.13 and rank-selection inputs.
The final source involution assembly belongs to qt-14-07-72-core-source-involution.

This application is a separate leaf: CubicTorus itself imports
SourceInvolution.Basic directly, so the geometry can be re-exported by the
source involution owner without an assembly cycle.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.70, printed p.1073, and 14.7.72, printed p.1076.
-/

public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The source involution consumer with its cubic geometry constructed.
S≤L₁ remains the independent parabolic-support producer's premise. -/
theorem exists_source_involution_of_earlier_cubic (c : CriticalPath (L := L) F)
    (earlier : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (actors : MarkedSpans.LocalActors d)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) (hU0 : d.U₀ = F.Vi 1)
    (hSP : S F L ≤ F.Li L 1)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hSQ : S F L ≤ Q T L)
    (selection : c.RankSelection)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα)
    (hF9α : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1) :
    ∃ u : c.Uα, orderOf u = 2 ∧ ∃ h : F.H,
      (h : G) * u * (h : G)⁻¹ ∈ F.H.pCoreIn 2 ∧
      (h : G) * u * (h : G)⁻¹ ∈ (F.Li L 1).pCoreIn 2 ∧
      (h : G) * u * (h : G)⁻¹ ∉ Q T L := by
  obtain ⟨geometry⟩ := CubicTorus.exists_torusGeometry_of_earlier d c earlier mark actors
    duality hcomm hU0
  exact exists_source_involution_of_earlier_torus d c earlier geometry hSP hTL hSQ
    mark selection hUH heven hF9 hF9α

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution
