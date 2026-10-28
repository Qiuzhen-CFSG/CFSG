module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersThompsonSourceSplitting
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentA314
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentPreparation

/-!
# TerminalComponentProperSource at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentProperSource`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
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

theorem proper_component_eq_residual_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.LocalAnalysis) : F.E = P.K := by
  let E : SY.NaturalCoordinates :=
    ⟨DY.model.coordinates,fun l v => by
      simpa only [DY.component_action] using
        DY.model.equivariant ⟨l,SY.chosen.normalizes l.property⟩ v⟩
  have hs : SY.NaturalOmegaDecomposition :=
    (E.core_omega_decomposition_of_weight_six_at structural escape (by
      intro z _ hz
      apply DY.pointCentralizers z ?_ (Or.inr hz)
      intro he
      have hh : weight (E.coordinates (1 : W)).toAdd.val = 0 := by
        simp only [map_one]; rfl
      rw [he] at hz
      omega)).1
  exact P.proper_component_eq_residual_of_natural_omega_source_at structural R F hKY SY E hs
    (fun he => F.Le_le_of_eq_maximal SY he)

theorem pointCentralizer_normalizes_of_residual_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (R : P.ResidualAnalysis) : P.pointCentralizer ≤ normalizer (P.K : Set G) := by
  obtain ⟨F⟩ := P.overcomponents_nonempty R.local_mem
  have hKY : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  by_cases he : P.K = F.Y
  · exact P.pointCentralizer_normalizes_of_maximal (he.symm ▸ F.maximal)
  · obtain ⟨W,⟨SY⟩⟩ := (R.overgroups F.Y F.maximal hKY).2.resolve_left he
    obtain ⟨DY⟩ := localAnalysis_at F.Y W SY
    have hE := P.proper_component_eq_residual_source_at structural escape R F
      (lt_of_le_of_ne hKY he) SY DY
    exact hE ▸ F.normalizes

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

