module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperRigidity
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentPreparation

/-!
# TerminalComponentProperRigidity at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentProperRigidity`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable {P : TerminalPoint S D}

namespace A314RestrictionInput

end A314RestrictionInput

theorem proper_component_eq_residual_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (A : A314RestrictionInput (P := P))
    (hLe : F.E = F.Y → P.Le ≤ F.Y)
    (hunique : AmbientA5Uniqueness (P := P) F) :
    F.E = P.K := by
  by_contra hne
  have hKE : P.K < F.E := lt_of_le_of_ne F.residual_le (Ne.symm hne)
  have hKYle : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  have hsetup : ∃ W' : Subgroup G, Nonempty (Setup T F.Y W') :=
    (R.overgroups F.Y F.maximal hKYle).2.resolve_left (ne_of_lt hKY)
  have hEY : F.E = F.Y := A.eq_maximal F hKE hsetup
  have hLeY : P.Le ≤ F.Y := hLe hEY
  have hKLe : P.K ≤ P.Le := hunique SY hEY hLeY
  exact P.residual_escape_at structural
    (hKLe.trans ((Le_le_original (P := P)).trans L.le_normalizer))

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

