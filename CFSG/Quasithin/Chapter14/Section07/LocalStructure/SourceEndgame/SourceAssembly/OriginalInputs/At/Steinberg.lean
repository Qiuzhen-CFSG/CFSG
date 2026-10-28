module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.Steinberg
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.ChiefCount

/-!
# The original 14.7.72 Steinberg and core conclusions

The actual three-factor count recognizes S/V. Parabolic support and the
original cubic involution exclude the double cover and identify S with O₂(L).
Only the structural input at the original G,T is used. Earlier-source
construction and final discharge remain with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.71–75, printed pp.1075–1078.
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

/-- Construct recognition, parabolic support, involution and core identity. -/
theorem finish_steinberg_and_core_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (actors : MarkedSpans.LocalActors d)
    (gen : SourceGeneration.Conclusion d)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (selection : c.RankSelection) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) : Conclusion72 d := by
  have hTL := d.natural.sylow_normalizes_at structural
  have hSQ : S F L ≤ Q T L := ChiefFactors.QKPlacement.S_le_Q_at d structural e.separation
  let := quotient_normal gen.frattini_eq
  let := quotient_elementary hSQ gen.frattini_eq
  let a := quotientAction d hTL gen.core_commutator.le
  obtain ⟨X,aX,mX,hs⟩ := CriticalIntersections.exists_sourceDuality d e.sectionCentralizer
  let := aX
  let := mX
  obtain ⟨duality⟩ := hs
  obtain ⟨b⟩ := ChiefFactors.HAccounting.exists_qKDualCoordinates d e.sectionCentralizer duality hcomm
  have hcount := ChiefFactors.QKPlacement.SourceCompletion.source_71_count_at d structural c e mark
    gen.fixed_kernel b a
  obtain ⟨s⟩ := ParabolicSteinberg.recognized_of_source_count d a hTL e.separation gen.fixed_kernel hcount
  have h71 : ⁅Q T L,L⁆ ≤ S F L :=
    ChiefFactors.QKPlacement.SourceCompletion.commutator_Q_L_le_S_at d structural c e mark b
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

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
