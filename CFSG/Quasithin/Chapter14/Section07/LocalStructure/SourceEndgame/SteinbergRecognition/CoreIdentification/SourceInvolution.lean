module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.Sections

/-!
# Source application of the critical-involution construction

The same original critical path, rank selection, upper marking and reciprocal
F.9.13 bounds give the commutator needed to select an involution in Uα∩Q_H.
The action descent is constructed from the earlier section-centralizer identity.
The second theorem applies the coprime parabolic capture and returns exactly
the existential consumed by `core_and_commutator_of_critical_conjugate`.

Both the cubic torus geometry and S≤L₁ remain explicit pending constructions.
Thus this is a conditional source connection, not completion of 14.7.72.
All subgroup inclusions and the left-conjugation expression retain the
original H, Q, L₁ and Uα. O₂(L₁) denotes its two-core.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.70, printed p.1073, and 14.7.72, printed p.1076 (PDF p.1093).
-/

public section
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

/-- The original critical kernel supplies a noncentral involution from the
actual earlier rank selection, quotient marking and reciprocal bounds. -/
theorem exists_critical_involution_of_earlier (c : CriticalPath (L := L) F)
    (earlier : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (selection : c.RankSelection)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα)
    (hF9α : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1) :
    ∃ u : c.Uα, orderOf u = 2 ∧ (u : G) ∈ F.H.pCoreIn 2 ∧
      (u : G) ∉ centralizer (F.U : Set G) := by
  let s : d.ActionDescent := {
    action := d.descendedAction earlier.sectionCentralizer
    original := d.descendedAction_apply earlier.sectionCentralizer }
  exact exists_critical_involution d c
    (opening_commutators d c earlier.images s mark selection earlier.image_order
      hUH heven hF9 hF9α).2.1

/-- This conditional source application leaves precisely the torus geometry
and S≤L₁ to their independent producers. It does not assume an involution
or an element-placement assertion. -/
theorem exists_source_involution_of_earlier_torus (c : CriticalPath (L := L) F)
    (earlier : ChiefFactors.Earlier d c)
    (g : TorusGeometry F L) (hSP : S F L ≤ F.Li L 1)
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
  let s : d.ActionDescent := {
    action := d.descendedAction earlier.sectionCentralizer
    original := d.descendedAction_apply earlier.sectionCentralizer }
  exact exists_source_involution_of_torus d c earlier g hSP hTL hSQ
    (opening_commutators d c earlier.images s mark selection earlier.image_order
      hUH heven hF9 hF9α).2.1
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution
