module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperLeCubics
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentA314
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceSplitting

/-!
# Relative normality of the escaping residual

For the proper maximal overcomponent, its original local analysis supplies
the natural coordinates and weight-six centralizer bound. Source 12.3.7
then gives the literal omega-center decomposition. Cubic generation of the
original L_e discharges its containment premise, allowing A.3.14 and the
ambient uniqueness argument to prove that the point-centralizer component
is exactly K. The maximal case follows from local-component maximality.

ResidualAnalysis remains the explicit 12.2.7 input owned by
qt-d-1231-terminal-component. This file completes the relative-normality
branch; the residual recognition and the proper branch's literal A₅ module
and Thompson-action conclusions remain with that same final assembly.

Source: Aschbacher--Smith, 12.3.7 and 12.3.12, printed pp.809 and 811.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- Relative normality in the proper branch, with both earlier source inputs
 supplied by the original local analysis of the same overcomponent. -/
theorem proper_component_eq_residual_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.LocalAnalysis) : F.E = P.K := by
  let E : SY.NaturalCoordinates :=
    ⟨DY.model.coordinates,fun l v => by
      simpa only [DY.component_action] using
        DY.model.equivariant ⟨l,SY.chosen.normalizes l.property⟩ v⟩
  have hs : SY.NaturalOmegaDecomposition :=
    (E.core_omega_decomposition_of_weight_six structural escape (by
      intro z _ hz
      apply DY.pointCentralizers z ?_ (Or.inr hz)
      intro he
      have hh : weight (E.coordinates (1 : W)).toAdd.val = 0 := by
        simp only [map_one]; rfl
      rw [he] at hz
      omega)).1
  exact P.proper_component_eq_residual_of_natural_omega_source structural R F hKY SY E hs
    (fun he => F.Le_le_of_eq_maximal SY he)
/-- Residual recognition suffices for normality in the literal point centralizer.
The maximal case uses local-component maximality; the proper case uses the
source cubic containment, A.3.14 and the actual 12.3.7 decomposition. -/
theorem pointCentralizer_normalizes_of_residual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (R : P.ResidualAnalysis) : P.pointCentralizer ≤ normalizer (P.K : Set G) := by
  obtain ⟨F⟩ := P.overcomponents_nonempty R.local_mem
  have hKY : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  by_cases he : P.K = F.Y
  · exact P.pointCentralizer_normalizes_of_maximal (he.symm ▸ F.maximal)
  · obtain ⟨W,⟨SY⟩⟩ := (R.overgroups F.Y F.maximal hKY).2.resolve_left he
    obtain ⟨DY⟩ := localAnalysis F.Y W SY
    have hE := P.proper_component_eq_residual_source structural escape R F
      (lt_of_le_of_ne hKY he) SY DY
    exact hE ▸ F.normalizes
end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
