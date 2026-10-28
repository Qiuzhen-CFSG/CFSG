module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.ParabolicSupport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution

/-!
# Applying parabolic support to the original source involution

The proved S≤L₁ discharges the literal containment premise of
SourceInvolution.exists_source_involution_of_earlier_torus. The original
critical path, quotient maps, earlier source inputs and TorusGeometry remain
unchanged. The cubic-torus producer and the enclosing 14.7.72 owner discharge
their respective geometry and earlier generation inputs.

This terminal application imports SourceInvolution; the reusable
ParabolicSupport leaf imports only SourceInvolution.Basic. Re-export the
support leaf from SourceInvolution, not this terminal application.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.72, printed p.1076 (PDF p.1093), using the opening deduction of 14.7.73.
-/

public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.ParabolicSupport
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

/-- The existing source involution application with its parabolic support
proved. TorusGeometry remains the independent cubic-torus input. -/
theorem exists_source_involution_of_earlier_torus (c : CriticalPath (L := L) F)
    (earlier : ChiefFactors.Earlier d c) (s : SteinbergCoordinates d)
    (g : TorusGeometry F L)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hSQ : S F L ≤ Q T L)
    (mark : UpperMarking d) (selection : c.RankSelection)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα)
    (hF9α : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1) :
    ∃ u : c.Uα, orderOf u = 2 ∧ ∃ h : F.H,
      (h : G) * u * (h : G)⁻¹ ∈ F.H.pCoreIn 2 ∧
      (h : G) * u * (h : G)⁻¹ ∈ (F.Li L 1).pCoreIn 2 ∧
      (h : G) * u * (h : G)⁻¹ ∉ Q T L := by
  exact SourceInvolution.exists_source_involution_of_earlier_torus d c earlier g
    (S_le_parabolic d s hPhi hSQ hTL) hTL hSQ mark selection hUH heven hF9 hF9α

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.ParabolicSupport
